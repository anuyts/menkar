{-# LANGUAGE GeneralizedNewtypeDeriving, NoDeriveAnyClass, UndecidableInstances #-}

module Menkar.Monads.DTT where

import Menkar.Basic
import Menkar.Fine.Syntax
import Menkar.Fine.Context
import Menkar.Systems.Trivial.Fine
import Menkar.Monad.Monad
import Menkar.TC.Judgement
import qualified Menkar.Raw as Raw
import qualified Menkar.PrettyPrint.Raw as Raw
import Menkar.PrettyPrint.Fine
import Menkar.PrettyPrint.Aux.Context

import Text.PrettyPrint.Tree
import Control.Exception.AssertFalse
import Control.Monad.MCont
import Data.Omissible

import GHC.Generics (U1 (..))
import Data.Void
import Data.Maybe
import Data.Either
import Data.Functor.Identity
import Data.Functor.Compose
import Data.Proxy
import Data.IntMap.Strict
import Data.Foldable
import Data.Monoid
import Control.Monad.Cont
--import Control.Monad.Trans.Cont
import Control.Monad.State.Lazy
import Control.Monad.List
import Control.Monad.Except
import Control.Monad.Fail
import Control.Lens
--import Data.Coerce
import Unsafe.Coerce

type TCResult = () --TCSuccess | TCWaiting

data SolutionInfo m v = SolutionInfo {
  _solutionInfo'parent :: Constraint Trivial,
  _solutionInfo'solution :: Term Trivial v
  }

data BlockInfo m v = BlockInfo {
  _blockInfo'parent :: Constraint Trivial,
  _blockInfo'reasonBlock :: String,
  _blockInfo'reasonAwait :: String,
  _blockInfo'cont :: (Maybe (Term Trivial v) -> TCT m TCResult)
  }

data MetaInfo m v = MetaInfo {
  _metaInfo'maybeParent :: Maybe (Constraint Trivial),
  _metaInfo'context :: Ctx Type Trivial v Void,
  --_metaInfo'deg :: U1 v,
  _metaInfo'reason :: String,
  {-| If solved, info about the solution.
      If unsolved, a list of blocked problems, from new to old, from outermost to innermost.
  -}
  _metaInfo'maybeSolution :: Either [([Int {- all metas blocking this thing -}], BlockInfo m v)] (SolutionInfo m v)
  }
isDormant :: MetaInfo m v -> Bool
isDormant metaInfo = case _metaInfo'maybeSolution metaInfo of
  Left [] -> True
  _ -> False
isBlockingStuff :: MetaInfo m v -> Bool
isBlockingStuff metaInfo = case _metaInfo'maybeSolution metaInfo of
  Left [] -> False
  Left _ -> True
  Right _ -> False
isSolved (MetaInfo maybeParent gamma reason maybeSolution) = isRight maybeSolution

data TCReport = TCReport {
  _tcReport'parent :: Constraint Trivial,
  _tcReport'reason :: String
  }

data TCState m = TCState {
  _tcState'metaCounter :: Int,
  _tcState'metaMap :: IntMap (ForSomeDeBruijnLevel (MetaInfo m)),
  _tcState'constraintCounter :: Int,
  _tcState'constraintMap :: IntMap (Constraint Trivial),
  _tcState'reports :: [TCReport],
  _tcState'newTasks :: [TCT m ()], -- always empty unless during constraint check; to be run from back to front
  _tcState'tasks :: [TCT m ()] -- to be run from front to back
  }
initTCState :: TCState m
initTCState = TCState 0 empty 0 empty [] [] []

{-
-- | delimited continuation monad class
class Monad m => MonadDC r m | m -> r where
  shiftDC :: ((a -> m r) -> m r) -> m a
  resetDC :: m r -> m r
instance Monad m => MonadDC r (ContT r m) where
  shiftDC f = ContT $ \ k -> f (lift . k) `runContT` return
  resetDC = lift . evalContT
-}

instance (MonadError e m) => MonadError e (ContT r m) where
  throwError e = lift $ throwError e
  -- CAREFUL: this also catches errors thrown in the future, i.e. by the continuation!!!
  catchError cma handle = ContT $ \k -> catchError (runContT cma k) (\e -> runContT (handle e) k)

data TCError m =
  TCErrorConstraintBound |
  {-| The outermost blocked @awaitMeta@ is first in the list. -}
  TCErrorBlocked (Constraint Trivial) String [(Int, ForSomeDeBruijnLevel (BlockInfo m))] |
  TCErrorTCFail TCReport |
  TCErrorScopeFail String |
  TCErrorInternal (Maybe (Constraint Trivial)) String

newtype TCT m a = TCT {unTCT :: MContT TCResult (ExceptT (TCError m) (StateT (TCState m) ({-ListT-}  m))) a}
  deriving (Functor, Applicative, Monad, MonadState (TCState m), MonadError (TCError m), MonadDC TCResult)

instance (Monad m) => MonadFail (TCT m) where
  fail s = unreachable

getTCT :: (Monad m) => TCT m () -> TCState m -> m (Either (TCError m) TCResult, TCState m)
getTCT program initState = flip runStateT initState $ runExceptT $ evalMContT $ unTCT program
--getTCT program initState = flip runStateT initState $ evalMContT $ unTCT program

type TC = TCT Identity

--getTC :: TC () -> TCState Identity -> Except (TCError Identity) (TCResult, TCState Identity)
getTC :: TC () -> TCState Identity -> (Either (TCError Identity) TCResult, TCState Identity)
getTC program initState = runIdentity $ getTCT program initState

----------------------------------------------------------------------------
makeLenses ''MetaInfo
makeLenses ''BlockInfo
makeLenses ''TCState
makeLenses ''TCReport
----------------------------------------------------------------------------

addTask :: Monad m => TCT m () -> TCT m ()
addTask task = do
  tcState'newTasks %= (task :)

commitTasks :: Monad m => TCT m ()
commitTasks = do
  newTasks <- tcState'newTasks <<.= []
  tcState'tasks %= (reverse newTasks ++)

typeCheck :: Monad m => TCT m ()
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
    (task : moreTasks) -> do
      tcState'tasks .= moreTasks
      task
      typeCheck

instance {-# OVERLAPPING #-} (Monad m) => MonadScoper Trivial (TCT m) where
  
  annot4annot gamma qstring maybeArg = case (qstring, maybeArg) of
    (Raw.Qualified [] "~", Nothing) -> return AnnotImplicit
    _ -> scopeFail $ "Illegal annotation: " ++ (render
             (Raw.unparse' qstring \\\ (maybeToList $ ($? id) . fine2pretty (ctx2scCtx gamma) <$> maybeArg))
             $? id
           )

  newMetaTermNoCheck maybeParent deg gamma etaFlag maybeAlg reason = do
    meta <- tcState'metaCounter <<%= (+1)
    tcState'metaMap %= (insert meta $ ForSomeDeBruijnLevel $ MetaInfo maybeParent gamma reason (Left []))
    let depcies = Compose $ Var2 <$> listAll Proxy
    return $ Expr2 $ TermMeta etaFlag meta depcies (Compose maybeAlg)

  newMetaMode maybeParent gamma reason = return U1

  newMetaModty maybeParent gamma reason = return U1

  --scopeFail reason = TCT . lift . lift . throwError $ TCErrorScopeFail reason
  scopeFail reason = throwError $ TCErrorScopeFail reason

catchBlocks :: (Monad m) => TCT m TCResult -> TCT m TCResult
catchBlocks action = resetDC $ action `catchError` \case
  TCErrorBlocked blockParent blockReason blocks -> do
    let blockingMetas = fst <$> blocks
    -- Need to reverse, as we're moving a list by popping and pushing, hence reversing.
    sequenceA_ $ reverse blocks <&> \(meta, ForSomeDeBruijnLevel blockInfo) -> do
      tcState'metaMap . at meta . _JustUnsafe %= \(ForSomeDeBruijnLevel metaInfo) ->
        ForSomeDeBruijnLevel $ over (metaInfo'maybeSolution . _LeftUnsafe)
          ((blockingMetas, unsafeCoerce blockInfo) :) metaInfo
      {-
      maybeMetaInfo <- use $ tcState'metaMap . at meta
      case maybeMetaInfo of
        Nothing -> unreachable
        Just (ForSomeDeBruijnLevel metaInfo) -> _handleBlocks
      -}
  e -> throwError e

checkConstraintTC :: (Monad m) => Constraint Trivial -> TCT m ()
checkConstraintTC c = catchBlocks $ do
  checkConstraint c
  commitTasks
  
instance {-# OVERLAPPING #-} (Monad m) => MonadTC Trivial (TCT m) where
  
  --newConstraintID = tcState'constraintCounter <<%= (+1)
  defConstraint jud maybeParent reason = do
    i <- tcState'constraintCounter <<%= (+1)
    let constraint = Constraint jud maybeParent reason i
    tcState'constraintMap %= insert i constraint
    when (i > 1000000) $ tcFail constraint "I may be stuck in a loop."
    return constraint

  -- Constraints are saved upon creation, not now.
  -- In fact, addConstraint is not even called on all created constraints.
  addConstraint constraint = addTask $ checkConstraintTC constraint

  addNewConstraint jud maybeParent reason = addTask $ do
    constraint <- defConstraint jud maybeParent reason
    checkConstraintTC constraint

  addConstraintReluctantly constraint = todo

  solveMeta parent meta getSolution = do
    ForSomeDeBruijnLevel metaInfo <- use $ tcState'metaMap . at meta . _JustUnsafe
    case _metaInfo'maybeSolution metaInfo of
      Right _ -> throwError $ TCErrorInternal (Just parent) $ "Meta already solved: " ++ show meta
      Left blocks -> do
        solution <- getSolution $ _metaInfo'context metaInfo
        -- Unblock blocked constraints
        sequenceA_ $ blocks <&> \ block@(blockingMetas, BlockInfo blockParent reasonBlock reasonAwait k) -> do
          {- @meta@ is currently being solved.
             @block@ represents a problem blocked by this meta.
             @k@ expresses how to unblock the problem if THIS meta is solved.
             @blockingMetas@ is a list of other metas that can unblock this problem; they have their own @k@.
          -}
          -- Check whether this is the first meta (among those on which this constraint is blocked) to be resolved.
          allAreUnsolved <- fmap (not . getAny . fold) $ sequenceA $ blockingMetas <&>
            \blockingMeta -> fmap (Any . forThisDeBruijnLevel isSolved) $ use $
              tcState'metaMap . at blockingMeta . _JustUnsafe
          if allAreUnsolved
          -- If so, then unblock with the solution just provided
          then addTask $ catchBlocks $ k $ Just $ solution
          -- Else forget about this blocked constraint, it has been unblocked already.
          else return ()
        -- Save the solution
        tcState'metaMap . at meta . _JustUnsafe .=
          ForSomeDeBruijnLevel (set metaInfo'maybeSolution (Right $ SolutionInfo parent solution) metaInfo)

{-do
    maybeMetaInfo <- use $ tcState'metaMap . at meta
    case maybeMetaInfo of
      Nothing -> unreachable
      Just (ForSomeDeBruijnLevel (MetaInfo maybeParent gamma reason maybeEarlierSolution)) -> do
        case maybeEarlierSolution of
          Right _ -> unreachable
          Left blocks -> do
            solution <- getSolution gamma
            -- Unblock blocked constraints
            sequenceA_ $ blocks <&> \ (blockingMetas, BlockInfo blockParent reasonBlock reasonAwait k) -> do
              -- Check whether this is the first meta (among those on which this constraint is blocked) to be resolved.
              allAreUnsolved <- fmap (not . getAny . fold) $ sequenceA $ blockingMetas <&>
                \blockingMeta -> fmap (Any . forThisDeBruijnLevel isSolved) $ use $
                  tcState'metaMap . at blockingMeta . _JustUnsafe
              if allAreUnsolved
              -- If so, then unblock with the solution just provided
              then addTask $ catchBlocks $ k $ Just $ solution
              -- Else forget about this blocked constraint, it has been unblocked already.
              else return ()
            -- Save the solution
            tcState'metaMap . at meta .=
              Just (ForSomeDeBruijnLevel $ MetaInfo maybeParent gamma reason (Right $ SolutionInfo parent solution))
-}

  awaitMeta parent reasonAwait meta depcies = do
    maybeMetaInfo <- use $ tcState'metaMap . at meta
    case maybeMetaInfo of
      Nothing -> unreachable
      Just (ForSomeDeBruijnLevel (MetaInfo maybeParent gamma reasonMeta maybeSolution)) -> do
        case maybeSolution of
          Right (SolutionInfo parent solution) -> do
            return $ Just $ join $ (depcies !!) . fromIntegral . getDeBruijnLevel Proxy <$> solution
          Left blocks -> shiftDC $ \ k -> do
            -- Try to continue with an unsolved meta
            k Nothing `catchError` \case
              TCErrorBlocked blockParent blockReason blocks -> do
                -- kick out enclosed @awaitMeta@s waiting for the same meta; they should never be run as they would
                -- incorrectly assume that the current, enclosing, @awaitMeta@ yields no result yet.
                let blocks' = Prelude.filter (\(blockMeta, blockInfo) -> blockMeta /= meta) blocks
                let blockInfo = BlockInfo blockParent blockReason reasonAwait $
                      k . fmap (join . (fmap $ (depcies !!) . fromIntegral . getDeBruijnLevel (ctx'sizeProxy gamma)))
                -- append the current meta and continuation as a means to fix the situation in the future, and rethrow.
                throwError $ TCErrorBlocked blockParent blockReason ((meta, ForSomeDeBruijnLevel blockInfo) : blocks')
                -- throwError $ TCErrorBlocked blockParent blockReason (blocks ++ [(meta, ForSomeDeBruijnLevel blockInfo)])
                --tcState'metaMap . at meta .=
                --  (Just $ ForSomeDeBruijnLevel $ MetaInfo maybeParent gamma reason $ Left $ block : blocks)
              e -> throwError e
  
  tcBlock parent reason = throwError $ TCErrorBlocked parent reason []

  tcReport parent reason = tcState'reports %= (TCReport parent reason :)
  
  tcFail parent reason = throwError $ TCErrorTCFail (TCReport parent reason)

  --leqMod U1 U1 = return True

{-
  selfcontained parent ma = addTask $ selfcontainedNoSched parent $ do
    ma
    typeCheck

selfcontainedNoSched :: (Monad m) =>
  Constraint Trivial -> TCT m a -> TCT m a
selfcontainedNoSched parent (TCT ma) = TCT $ mapMContT (selfcontainedNoContNoSched parent) ma

selfcontainedNoContNoSched :: (Monad m) =>
  Constraint Trivial ->
  ExceptT (TCError m) (StateT (TCState m) m) a ->
  ExceptT (TCError m) (StateT (TCState m) m) a
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

