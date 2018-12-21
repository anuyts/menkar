{-# LANGUAGE GeneralizedNewtypeDeriving, NoDeriveAnyClass, UndecidableInstances #-}

module Menkar.TC.Monad.DTT where

import Menkar.Basic
import Menkar.Fine.Syntax
import Menkar.Fine.Context
import Menkar.Fine.Multimode.Trivial
import Menkar.TC.Monad
import Menkar.TC.Inference
import qualified Menkar.Raw as Raw
import qualified Menkar.PrettyPrint.Raw as Raw
import Menkar.PrettyPrint.Fine
import Menkar.PrettyPrint.Aux.Context

import Text.PrettyPrint.Tree
import Control.Exception.AssertFalse
import Control.Monad.MCont

import GHC.Generics (U1 (..))
import Data.Void
import Data.Maybe
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
import Control.Lens

type TCResult = () --TCSuccess | TCWaiting

data SolutionInfo m v = SolutionInfo {
  _solutionInfo'parent :: Constraint U1 U1 U1,
  _solutionInfo'solution :: Term U1 U1 v
  }

data BlockInfo m v = BlockInfo {
  _blockInfo'reason :: String,
  _blockInfo'cont :: (Maybe (Term U1 U1 v) -> TCT m TCResult)
  }

data MetaInfo m = forall v . (DeBruijnLevel v) => MetaInfo {
  _metaInfo'maybeParent :: Maybe (Constraint U1 U1 U1),
  _metaInfo'context :: Ctx Type U1 U1 v Void,
  --_metaInfo'deg :: U1 v,
  _metaInfo'reason :: String,
  _metaInfo'maybeSolution :: Either [BlockInfo m v] (SolutionInfo m v)
  }
isDormant :: MetaInfo m -> Bool
isDormant (MetaInfo maybeParent gamma reason maybeSolution) = case maybeSolution of
  Left [] -> True
  _ -> False
isBlockingStuff :: MetaInfo m -> Bool
isBlockingStuff (MetaInfo maybeParent gamma reason maybeSolution) = case maybeSolution of
  Left [] -> False
  Left _ -> True
  Right _ -> False

data TCReport = TCReport {
  _tcReport'parent :: Constraint U1 U1 U1,
  _tcReport'reason :: String
  }

data TCState m = TCState {
  _tcState'metaCounter :: Int,
  _tcState'metaMap :: IntMap (MetaInfo m),
  _tcState'constraintCounter :: Int,
  _tcState'reports :: [TCReport]
  }

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
  TCErrorBlocked String |
  TCErrorTCFail TCReport (TCState m) |
  TCErrorScopeFail String

newtype TCT m a = TCT {unTCT :: MContT TCResult (StateT (TCState m) ({-ListT-} (ExceptT (TCError m) m))) a}
  deriving (Functor, Applicative, Monad, MonadState (TCState m), MonadError (TCError m), MonadDC TCResult)

runTCT :: (Monad m) => TCT m () -> TCState m -> ExceptT (TCError m) m (TCResult, TCState m)
runTCT program initState = flip runStateT initState $ evalMContT $ unTCT program

type TC = TCT Identity

runTC :: TC () -> TCState Identity -> Except (TCError Identity) (TCResult, TCState Identity)
runTC = runTCT

----------------------------------------------------------------------------
makeLenses ''MetaInfo
makeLenses ''BlockInfo
makeLenses ''TCState
makeLenses ''TCReport
----------------------------------------------------------------------------

instance {-# OVERLAPPING #-} (Monad m) => MonadScoper U1 U1 U1 (TCT m) where
  
  annot4annot gamma qstring args = case (qstring, args) of
    (Raw.Qualified [] "~", []) -> return AnnotImplicit
    _ -> scopeFail $ "Illegal annotation: " ++ (render defaultRenderState $
             Raw.unparse' qstring \\\ fine2pretty (ctx2scCtx gamma) <$> args
           )

  newMetaTermNoCheck maybeParent deg gamma reason = do
    meta <- tcState'metaCounter <<%= (+1)
    tcState'metaMap %= (insert meta $ MetaInfo maybeParent gamma reason (Left []))
    let depcies = Compose $ Var3 <$> listAll Proxy
    return $ Expr3 $ TermMeta meta depcies

  newMetaMode maybeParent gamma reason = return U1

  newMetaModty maybeParent gamma reason = return U1

  scopeFail reason = TCT . lift . lift . throwError $ TCErrorScopeFail reason

instance {-# OVERLAPPING #-} (Monad m) => MonadTC U1 U1 U1 (TCT m) where
  
  newConstraintID = tcState'constraintCounter <<%= (+1)

  addConstraint constraint = resetDC $ do
    -- I'm not saving the constraint, as addConstraint is not even called on all created constraints.
    -- If you want to save it, you should ask the whereabouts in newConstraintID,
    -- since you should only entrust someone an ID if you're sure they're registering the constraint.
    checkConstraint constraint

  addConstraintReluctantly constraint = todo

  solveMeta parent meta getSolution = do
    maybeMetaInfo <- use $ tcState'metaMap . at meta
    case maybeMetaInfo of
      Nothing -> unreachable
      Just (MetaInfo maybeParent gamma reason maybeEarlierSolution) -> do
        case maybeEarlierSolution of
          Right _ -> unreachable
          Left blocks -> do
            solution <- getSolution gamma
            sequenceA_ $ blocks <&> \ (BlockInfo reason k) -> resetDC $ k $ Just $ solution
            tcState'metaMap . at meta .= Just (MetaInfo maybeParent gamma reason (Right $ SolutionInfo parent solution))

  awaitMeta parent reason meta depcies = do
    maybeMetaInfo <- use $ tcState'metaMap . at meta
    case maybeMetaInfo of
      Nothing -> unreachable
      Just (MetaInfo maybeParent gamma reason maybeSolution) -> do
        case maybeSolution of
          Right (SolutionInfo parent solution) -> do
            return $ Just $ join $ (depcies !!) . fromIntegral . getDeBruijnLevel Proxy <$> solution
          Left blocks -> shiftDC $ \ k -> do
            -- Try to continue with an unsolved meta
            k Nothing `catchError` \case
              TCErrorBlocked blockReason -> do
                let block = BlockInfo reason $
                            k . fmap (join . (fmap $ (depcies !!) . fromIntegral . getDeBruijnLevel Proxy))
                tcState'metaMap . at meta .=
                  (Just $ MetaInfo maybeParent gamma reason $ Left $ block : blocks)
              e -> throwError e
  
  tcBlock reason = throwError $ TCErrorBlocked reason

  tcReport parent reason = tcState'reports %= (TCReport parent reason :)
  
  tcFail parent reason = do
    s <- get
    throwError $ TCErrorTCFail (TCReport parent reason) s

  leqMod U1 U1 = return True
  
  selfcontained parent (TCT ma) = TCT $ mapMContT (selfcontainedNoCont parent) ma

selfcontainedNoCont :: (Monad m) =>
  Constraint U1 U1 U1 ->
  StateT (TCState m) (ExceptT (TCError m) m) a ->
  StateT (TCState m) (ExceptT (TCError m) m) a
selfcontainedNoCont parent ma = do
  -- Metas on which nothing is blocked (=: dormant meta), may be future metas already introduced by the scopechecker
  -- Thus, we need to check that
  state0 <- get
  let metaCount0 = _tcState'metaCounter state0
  a <- ma
  state1 <- get
  let metaCount1 = _tcState'metaCounter state1
  let throwTheError = throwError $ TCErrorTCFail (
        TCReport parent "The meaning of this judgement is not self-contained: it spills unsolved meta-variables."
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
