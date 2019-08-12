{-# LANGUAGE GeneralizedNewtypeDeriving, NoDeriveAnyClass, UndecidableInstances #-}

module Menkar.Monads.DTT where

import Menkar.Basic
import Menkar.ID
import Menkar.Fine.Syntax
import Menkar.Fine.Context
import Menkar.Fine.LookupQName
--import Menkar.Systems.Trivial.Trivial
import Menkar.Monad.Monad
import Menkar.TC.Judgement
import qualified Menkar.Raw as Raw
import qualified Menkar.PrettyPrint.Raw as Raw
import Menkar.PrettyPrint.Fine
import Menkar.PrettyPrint.Aux.Context
import Menkar.System
import Menkar.Fine.Judgement
import Menkar.Analyzer.Class

import Text.PrettyPrint.Tree
import Control.Exception.AssertFalse
--import Control.Monad.MCont
import Data.Omissible
import Data.Functor.Functor1
import Control.Monad.LoopReturn

import GHC.Generics
import Data.Void
import Data.Maybe
import Data.Either
import Data.Functor.Identity
import Data.Functor.Compose
import Data.IntMap.Strict
import Data.Foldable
import Data.Monoid
import Control.Monad.Cont
import Control.Monad.Trans.Cont
import Control.Monad.Trans.Reader hiding (ask)
import Control.Monad.Reader.Class
import Control.Monad.State.Strict
import Control.Monad.List
import Control.Monad.Except
import Control.Monad.Fail
import Control.Lens
--import Data.Coerce
import Unsafe.Coerce
import Data.Kind hiding (Constraint, Type)
import Data.List hiding (insert)
import Data.List.Utils (mergeBy)
import Data.Ord

type TCResult (sys :: KSys) = () --TCSuccess | TCWaiting

data SolutionInfo (sys :: KSys) (m :: * -> *) (v :: *) = SolutionInfo {
  _solutionInfo'parent :: Constraint sys,
  _solutionInfo'solution :: ForSomeSolvableAST sys v
  }

data BlockingMeta (sys :: KSys) (m :: * -> *) (v :: *) = BlockingMeta {
  _blockingMeta'meta :: Int,
  _blockingMeta'cont :: (ForSomeSolvableAST sys v -> TCT sys m (TCResult sys)),
  _blockingMeta'reasonAwait :: String
  }

data Worry (sys :: KSys) (m :: * -> *) = Worry {
  _worry'constraint :: Constraint sys,
  {-| From outermost to innermost. -}
  _worry'metas :: [ForSomeDeBruijnLevel (BlockingMeta sys m)],
  {-| Whether a judgement has been scheduled (but may not yet have been created) to unblock this worry. -}
  _worry'unblockScheduled :: Bool,
  {-| Nothing if still blocked, otherwise the meta that unblocked it. -}
  _worry'unblockedBy :: Maybe MetaID,
  {-| A @JudUnblock@, if already scheduled. Note that the existence of this judgement does not imply that it has
      already been processed. (Actually it does in the current implementation, but let's not count on that.) -}
  _worry'constraintUnblock :: Maybe (Constraint sys),
  _worry'reason :: String
  }

{-
data BlockInfo (sys :: KSys) (m :: * -> *) (v :: *) = BlockInfo {
  _blockInfo'parent :: Constraint sys,
  _blockInfo'reasonBlock :: String,
  _blockInfo'reasonAwait :: String,
  _blockInfo'cont :: (Maybe (Term sys v) -> TCT sys m (TCResult sys))
  }
-}

data MetaInfo (sys :: KSys) m v = MetaInfo {
  _metaInfo'maybeParent :: Maybe (Constraint sys),
  _metaInfo'context :: Ctx Type sys v,
  --_metaInfo'deg :: U1 v,
  _metaInfo'reason :: String,
  {-| If solved, info about the solution.
      If unsolved, a list of blocked problems, from new to old, from outermost to innermost.
  -}
  _metaInfo'maybeSolution :: Either
    [WorryID] {- All blocks blocked on the current, unsolved meta. -}
    (SolutionInfo sys m v)
  }
isDormant :: MetaInfo sys m v -> Bool
isDormant metaInfo = case _metaInfo'maybeSolution metaInfo of
  Left [] -> True
  _ -> False
isBlockingStuff :: MetaInfo sys m v -> Bool
isBlockingStuff metaInfo = case _metaInfo'maybeSolution metaInfo of
  Left [] -> False
  Left _ -> True
  Right _ -> False
isSolved (MetaInfo maybeParent gamma reason maybeSolution) = isRight maybeSolution

data TCReport sys = TCReport {
  _tcReport'parent :: Constraint sys,
  _tcReport'reason :: String
  }

data TCOptions = TCOptions {
  _tcOptions'loop :: Int
  }

data TCState sys m = TCState {
  _tcState'metaCounter :: Int,
  _tcState'metaMap :: IntMap (ForSomeDeBruijnLevel (MetaInfo sys m)),
  _tcState'constraintCounter :: Int,
  _tcState'constraintMap :: IntMap (Constraint sys),
  _tcState'worryCounter :: Int,
  _tcState'worryMap :: IntMap (Worry sys m),
  _tcState'reports :: [(TCReport sys)],
  _tcState'newTasks :: [(PriorityConstraint, TCT sys m ())],
    -- ^ always empty unless during constraint check; to be run from back to front
  _tcState'tasks :: [(PriorityConstraint, TCT sys m ())],
    -- ^ to be run from front to back
  _tcState'maybeParent :: Maybe (Constraint sys)
  }
initTCState :: TCState sys m
initTCState = TCState 0 empty 0 empty 0 empty [] [] [] Nothing

-- | delimited continuation monad class
class Monad m => MonadDC r m | m -> r where
  shiftDC :: ((a -> m r) -> m r) -> m a
  resetDC :: m r -> m r
instance Monad m => MonadDC r (ContT r m) where
  shiftDC f = ContT $ \ k -> f (lift . k) `runContT` return
  resetDC = lift . evalContT

instance (MonadError e m) => MonadError e (ContT r m) where
  throwError e = lift $ throwError e
  -- CAREFUL: this also catches errors thrown in the future, i.e. by the continuation!!!
  catchError cma handle = ContT $ \k -> catchError (runContT cma k) (\e -> runContT (handle e) k)

data TCError sys m =
  TCErrorConstraintBound |
  {-| The outermost blocked @awaitMeta@ is first in the list. -}
  TCErrorBlocked (Constraint sys) String [ForSomeDeBruijnLevel (BlockingMeta sys m)] |
  TCErrorTCFail (TCReport sys) |
  TCErrorScopeFail String |
  TCErrorInternal (Maybe (Constraint sys)) String

newtype TCT (sys :: KSys) (m :: * -> *)  (a :: *) =
  TCT {unTCT :: ContT (TCResult sys) (ExceptT (TCError sys m) (StateT (TCState sys m) (ReaderT TCOptions ({-ListT-}  m)))) a}
  deriving (Functor, Applicative, Monad,
            MonadState (TCState sys m),
            MonadError (TCError sys m),
            MonadDC (TCResult sys),
            MonadReader (TCOptions))

instance (Monad m) => MonadFail (TCT sys m) where
  fail s = unreachable

getTCT :: (Monad m) =>
  TCOptions ->
  TCState sys m ->
  TCT sys m () ->
  m (Either (TCError sys m) (TCResult sys), TCState sys m)
getTCT opts initState program = flip runReaderT opts $ flip runStateT initState $ runExceptT $ evalContT $ unTCT program
--getTCT program initState = flip runStateT initState $ evalContT $ unTCT program

type TC sys = TCT sys Identity

--getTC :: TC () -> TCState Identity -> Except (TCError Identity) (TCResult, TCState Identity)
getTC ::
  TCOptions ->
  TCState sys Identity ->
  TC sys () ->
  (Either (TCError sys Identity) (TCResult sys), TCState sys Identity)
getTC opts initState program = runIdentity $ getTCT opts initState program

----------------------------------------------------------------------------
makeLenses ''MetaInfo
makeLenses ''BlockingMeta
makeLenses ''Worry
makeLenses ''TCState
makeLenses ''TCReport
----------------------------------------------------------------------------

addTask :: Monad m => PriorityConstraint -> TCT sys m () -> TCT sys m ()
addTask priority task = do
  tcState'newTasks %= ((priority, task) :)

commitTasks :: Monad m => TCT sys m ()
commitTasks = do
  -- get the new tasks, reverse them, put the low priority ones last, and then insert them into the tasks by priority.
  newTasks <- tcState'newTasks <<.= []
  tcState'tasks %= mergeBy (comparing fst) (sortBy (comparing fst) $ reverse newTasks)

typeCheck :: Monad m => TCT sys m ()
typeCheck = do
  commitTasks -- just to be sure
  tasks <- use tcState'tasks
  --scopeFail "Mumblemaster"
  --when (Prelude.null tasks) unreachable
  --when (not $ Prelude.null tasks) unreachable
  --when False unreachable
  --when True unreachable
  --unreachable
  case tasks of
    [] -> return ()
    ((_, task) : moreTasks) -> do
      tcState'tasks .= moreTasks
      task
      typeCheck

instance {-# OVERLAPPING #-} (Monad m, SysTC sys, Degrees sys) => MonadScoper sys (TCT sys m) where

  newMetaID gamma reason = do
    maybeParent <- useMaybeParent
    meta <- tcState'metaCounter <<%= (+1)
    tcState'metaMap %= (insert meta $ ForSomeDeBruijnLevel $ MetaInfo maybeParent gamma reason (Left []))
    let depcies = Dependencies $ coy $ Compose $ forallVarsRev $ \ v ->
          let d = _modalityTo'dom $ _segment'modty $ _leftDivided'content $ uncoy $ lookupVar gamma v
          in  d :*: Var2 v
    return (meta, depcies)
    
  {-
  newMetaTermNoCheck maybeParent gamma neutrality maybeAlg reason = do
    meta <- tcState'metaCounter <<%= (+1)
    tcState'metaMap %= (insert meta $ ForSomeDeBruijnLevel $ MetaInfo maybeParent gamma reason (Left []))
    let depcies = Compose $ Var2 <$> listAllRev
    return $ Expr2 $ TermMeta neutrality meta depcies (Compose maybeAlg)
  -}

  --scopeFail reason = TCT . lift . lift . throwError $ TCErrorScopeFail reason
  scopeFail reason = throwError $ TCErrorScopeFail reason

catchBlocks :: (Monad m, SysTC sys) => TCT sys m (TCResult sys) -> TCT sys m (TCResult sys)
catchBlocks action = resetDC $ action `catchError` \case
  TCErrorBlocked blockParent blockReason blockingMetas -> do
    iD <- WorryID <$> (tcState'worryCounter <<%= (+1))
    constraintJudBlock <- withParent blockParent $ defConstraint (JudBlock iD) blockReason
    let worry = Worry constraintJudBlock blockingMetas False Nothing Nothing blockReason
    tcState'worryMap %= insert (getWorryID iD) worry
    -- Need to reverse, as we're moving a list by popping and pushing, hence reversing.
    sequenceA_ $ reverse blockingMetas <&> \blockingMeta -> do
      tcState'metaMap . at (forThisDeBruijnLevel _blockingMeta'meta blockingMeta) . _JustUnsafe
        %= \(ForSomeDeBruijnLevel metaInfo) ->
             ForSomeDeBruijnLevel $ (metaInfo'maybeSolution . _LeftUnsafe %~ (iD :)) metaInfo
  e -> throwError e

checkConstraintTC :: (SysTC sys, Degrees sys, Monad m) => Constraint sys -> TCT sys m ()
checkConstraintTC c = catchBlocks $ do
  checkConstraint c
  commitTasks

instance {-# OVERLAPPING #-} (SysTC sys, Degrees sys, Monad m) => MonadWHN sys (TCT sys m) where

  awaitMeta reasonAwait meta depcies = do
    maybeMetaInfo <- use $ tcState'metaMap . at meta
    case maybeMetaInfo of
      -- If a meta is awaited, then we assume it is created legally and the monad knows, so it's in the metaMap.
      Nothing -> unreachable
      -- Obtain MetaInfo.
      Just (ForSomeDeBruijnLevel (MetaInfo _ (gamma :: Ctx _ _ vOrig) reasonMeta maybeSolution)) -> do
        case maybeSolution of
          Right (SolutionInfo _ solution) -> do
            -- Substitute the dependencies into the solution and return.
            return $ Just $ substitute (depcies2subst @sys @vOrig depcies) . unsafeForceSolvableAST $ solution
          Left worryIDs -> shiftDC $ \ kCurrent -> do
            -- Prepend the continuation with substituting the dependencies into the solution.
            let kCurrentAdjusted = kCurrent
                  . fmap (substitute (depcies2subst @sys @vOrig depcies) . unsafeForceSolvableAST)
            let allowContinuationToBlockOnCurrentMeta :: forall x .
                  (x -> TCT sys m (TCResult sys)) ->
                  (x -> TCT sys m (TCResult sys))
                allowContinuationToBlockOnCurrentMeta kEnclosed x =
                  kEnclosed x `catchError` \case
                    TCErrorBlocked blockParent blockReason blockingMetas -> do
                      -- kick out enclosed @awaitMeta@s waiting for the same meta; they should never be run as they would
                      -- incorrectly assume that the current, enclosing, @awaitMeta@ yields no result yet.
                      let blockingMetas' = Prelude.filter
                            (\blockingMeta -> (forThisDeBruijnLevel _blockingMeta'meta blockingMeta) /= meta)
                            blockingMetas
                      -- allow continuations for enclosed @awaitMeta@s to block on the current meta as well!
                      let blockingMetas'' = blockingMetas' <&>
                            mapDeBruijnLevel (blockingMeta'cont %~ allowContinuationToBlockOnCurrentMeta)
                      -- append the current meta and continuation, and rethrow.
                      {- I think it doesn't matter whether kCurrentAdjusted below is allowed to block on current meta,
                         because it will only be called after the current meta has been solved.
                      -}
                      let currentBlockingMeta =
                            BlockingMeta meta ({-allowContinuationToBlockOnCurrentMeta-} kCurrentAdjusted . Just) reasonAwait
                      throwError $ TCErrorBlocked blockParent blockReason
                        (ForSomeDeBruijnLevel currentBlockingMeta : blockingMetas'')
                      -- throwError $ TCErrorBlocked blockParent blockReason
                      --                (blocks ++ [(meta, ForSomeDeBruijnLevel blockInfo)])
                      --tcState'metaMap . at meta .=
                      --  (Just $ ForSomeDeBruijnLevel $ MetaInfo maybeParent gamma reason $ Left $ block : blocks)
                    e -> throwError e
            -- Try to continue with an unsolved meta
            allowContinuationToBlockOnCurrentMeta kCurrentAdjusted Nothing

withMaybeParent :: (Monad m) => Maybe (Constraint sys) -> TCT sys m a -> TCT sys m a
withMaybeParent maybeParent action = do
    maybeOuterParent <- tcState'maybeParent <.= maybeParent
    result <- action
    tcState'maybeParent .= maybeOuterParent
    return result
  
instance {-# OVERLAPPING #-} (SysTC sys, Degrees sys, Monad m) => MonadTC sys (TCT sys m) where

  withParent parent action = withMaybeParent (Just parent) action

  useMaybeParent = use tcState'maybeParent
  
  --newConstraintID = tcState'constraintCounter <<%= (+1)
  defConstraint jud reason = do
    maybeParent <- useMaybeParent
    i <- tcState'constraintCounter <<%= (+1)
    let constraint = Constraint jud maybeParent reason i
    tcState'constraintMap %= insert i constraint
    loop <- _tcOptions'loop <$> ask
    when (i >= loop) $ withParent constraint $ tcFail "I may be stuck in a loop."
    return constraint

  -- Constraints are saved upon creation, not now.
  -- In fact, addConstraint is not even called on all created constraints.
  addConstraint constraint = addTask (getConstraintPriority constraint) $ checkConstraintTC constraint

  addNewConstraint jud reason = do
    maybeParent <- useMaybeParent
    addTask (getJudgementPriority jud) $ do
      constraint <- withMaybeParent maybeParent $ defConstraint jud reason
      checkConstraintTC constraint

  addConstraintReluctantly constraint = todo

  solveMeta meta getSolution = do
    -- Note: If you swap the following lines, then you get a GHC panic: "No skolem info."
    -- Get info for this meta
    ForSomeDeBruijnLevel metaInfo <- use $ tcState'metaMap . at meta . _JustUnsafe
    -- Get the parent judgement
    parent <- fromMaybe unreachable <$> useMaybeParent
    case _metaInfo'maybeSolution metaInfo of
      -- If it's solved, throw an error.
      Right _ -> do
        throwError $ TCErrorInternal (Just parent) $ "Meta already solved: " ++ show meta
      -- worryIDs contains the worries blocked on (among others) the current meta.
      Left worryIDs -> do
        -- Call the closure provided by the caller to obtain the solution for the meta.
        -- ('a' is just something that the caller wants back.)
        (maybeSolution, a) <- getSolution $ _metaInfo'context metaInfo
        case maybeSolution of
          -- If the caller fails to provide a solution, abort and pass back @a@.
          Nothing -> return a
          -- The caller provides @solution :: Term sys v@.
          Just solution -> do
            -- Save the solution
            tcState'metaMap . at meta . _JustUnsafe .= ForSomeDeBruijnLevel (
              metaInfo & metaInfo'maybeSolution .~ (Right $ SolutionInfo parent $ ForSomeSolvableAST solution)
              )
            -- Consider to unblock blocked constraints
            sequenceA_ $ worryIDs <&>
              {- @meta@ (introduced above) is currently being solved.
                 @block@ represents a problem blocked by this meta.
                 @k@ expresses how to unblock the problem if THIS meta is solved.
                 @blockingMetas@ is a list of other metas that can unblock this problem; they have their own @k@.
              -}
              -- \ block@(blockingMetas, BlockInfo blockParent reasonBlock reasonAwait k, constraintJudBlock) ->
              \ worryID -> do
                  -- Get the blocking constraint
                  worry <- use $
                    tcState'worryMap . at (getWorryID worryID) . _JustUnsafe
                  let unblockScheduled = _worry'unblockScheduled worry
                  let constraintJudBlock = _worry'constraint worry
                  unless unblockScheduled $ withParent constraintJudBlock $ do
                    -- Add an unblocking constraint, which will call tcUnblock
                    {-constraintJudUnblock <-
                      defConstraint (JudUnblock worryID) $ "Meta ?" ++ show meta ++ " has been resolved."
                    addConstraint constraintJudUnblock -}
                    addNewConstraint (JudUnblock worryID) $ "Meta ?" ++ show meta ++ " has been resolved."
                    -- Record that you have scheduled an unblocking constraint.
                    tcState'worryMap . at (getWorryID worryID) . _JustUnsafe . worry'unblockScheduled .= True
                    {- -- Register the unblocking constraint with the worry
                    tcState'worryMap . at (getWorryID worryID)
                      . _JustUnsafe . worry'constraintUnblock .= Just constraintJudUnblock-}
                  {-
                  -- Informative judgement: we consider to unblock.
                  constraintJudUnblock <- withParent constraintJudBlock $
                    defConstraint (JudUnblock meta) "A blocking meta has been resolved."
                  {- The metas are ordered from outer to inner.
                     If a meta outside of the current one is solved, then we should not do anything.
                     NOTE: forReturnList traverses a list until you return Nothing.
                  -}
                  outerSolveds <- forReturnList blockingMetas $ \ blockingMeta -> do
                    if blockingMeta == meta
                      then return Nothing
                      else Just . forThisDeBruijnLevel isSolved <$> use (tcState'metaMap . at blockingMeta . _JustUnsafe)
                  if or outerSolveds
                    then return ()
                    else withParent constraintJudUnblock $ catchBlocks $ k $ Just $ solution-}
            return a
  
  tcBlock reason = do
    parent <- fromMaybe unreachable <$> useMaybeParent
    throwError $ TCErrorBlocked parent reason []

  tcUnblock worryID = do
    maybeMeta <- use $ tcState'worryMap . at (getWorryID worryID) . _JustUnsafe
      . worry'unblockedBy
    case maybeMeta of
      Just meta -> return () -- This thing has been unblocked before.
      Nothing -> do
        constraintJudUnblock <- fromMaybe unreachable <$> useMaybeParent
        worry <- use $ tcState'worryMap . at (getWorryID worryID) . _JustUnsafe
        let blockingMetas = _worry'metas worry
        (_, maybeUnit) <- forReturnList blockingMetas $ \(ForSomeDeBruijnLevel blockingMeta) -> do
          let meta = _blockingMeta'meta blockingMeta
          ForSomeDeBruijnLevel metaInfo <- use $ tcState'metaMap . at meta . _JustUnsafe
          let maybeSolution = _metaInfo'maybeSolution metaInfo
          case maybeSolution of
            Left _ -> return $ Left ()
            Right solution -> do
              let t = _solutionInfo'solution solution
              tcState'worryMap . at (getWorryID worryID) . _JustUnsafe %=
                (worry'unblockedBy .~ (Just $ _blockingMeta'meta blockingMeta))
                .
                (worry'constraintUnblock .~ Just constraintJudUnblock)
              catchBlocks $ _blockingMeta'cont blockingMeta $ unsafeCoerce <$> t
              return $ Right ()
        case maybeUnit of
          Just () -> return ()
          Nothing -> tcFail $ "This is a bug: I'm asked to unblock a worry but all blocking metas are still unsolved."

  tcReport reason = do
    parent <- fromMaybe unreachable <$> useMaybeParent
    tcState'reports %= (TCReport parent reason :)
  
  tcFail reason = do
    parent <- fromMaybe unreachable <$> useMaybeParent
    throwError $ TCErrorTCFail (TCReport parent reason)

  --leqMod U1 U1 = return True

{-
  selfcontained parent ma = addTask $ selfcontainedNoSched parent $ do
    ma
    typeCheck

selfcontainedNoSched :: (Monad m) =>
  Constraint sys -> TCT sys m a -> TCT sys m a
selfcontainedNoSched parent (TCT ma) = TCT $ mapContT (selfcontainedNoContNoSched parent) ma

selfcontainedNoContNoSched :: (Monad m) =>
  Constraint sys ->
  ExceptT (TCError m) (StateT (TCState sys m) m) a ->
  ExceptT (TCError m) (StateT (TCState sys m) m) a
selfcontainedNoContNoSched parent ma = do
  -- Metas on which nothing is blocked (=: dormant meta), may be future metas already introduced by the scopechecker
  -- Thus, we need to check that
  state0 <- get
  let metaCount0 = _tcState'metaCounter state0
  a <- ma
  state1 <- get
  let metaCount1 = _tcState'metaCounter state1
  let spilledAwakenedMetas = fold $
        [0 .. metaCount0 - 1] <&> \ meta ->
          let dormant0 = forThisDeBruijnLevel isDormant $
                fromMaybe unreachable $ view (tcState'metaMap . at meta) state0
              blockingStuff1 = forThisDeBruijnLevel isBlockingStuff $
                fromMaybe unreachable $ view (tcState'metaMap . at meta) state1
          in  if dormant0 && blockingStuff1
              then [meta]
              else []
  let spilledNewMetas = fold $
        [metaCount0 .. metaCount1 - 1] <&> \ meta ->
          if forThisDeBruijnLevel isBlockingStuff $
                fromMaybe unreachable $ view (tcState'metaMap . at meta) state1
          then [meta]
          else []
  case (spilledAwakenedMetas ++ spilledNewMetas) of
    [] -> return a
    spilledMetas -> throwError $ TCErrorTCFail (
      TCReport parent (
          "The meaning of this declaration is not self-contained: it spills unsolved meta-variables:\n" ++
          (fold $ (" ?" ++) . show <$> spilledMetas)
        )
      )

  {-
  let throwTheError = throwError $ TCErrorTCFail (
        TCReport parent "The meaning of this declaration is not self-contained: it spills unsolved meta-variables."
        ) state1
  -- 1) Any dormant meta is either still dormant or solved,
  let spillsAwakenedMetas = getAny $ fold $ fmap Any $
        [0 .. metaCount0 - 1] <&> \ meta ->
          let dormant0 = isDormant $ fromMaybe unreachable $ view (tcState'metaMap . at meta) state0
              blockingStuff1 = isBlockingStuff $ fromMaybe unreachable $ view (tcState'metaMap . at meta) state1
          in  dormant0 && blockingStuff1
  when spillsAwakenedMetas $ throwTheError
  -- 2) Any newly introduced meta is solved.
  let spillsNewMetas = getAny $ fold $ fmap Any $
        [metaCount0 .. metaCount1 - 1] <&> \ meta ->
          isBlockingStuff $ fromMaybe unreachable $ view (tcState'metaMap . at meta) state1
  when spillsNewMetas $ throwTheError
  return a
  -}
-}

---------------------------

