{-# LANGUAGE UndecidableInstances #-}

module Menkar.TC.Monad.Monad where

import Menkar.Fine.Syntax
import Menkar.Fine.Judgement
import Menkar.Fine.Context
import Menkar.Fine.Multimode
import qualified Menkar.Raw.Syntax as Raw
import Menkar.Scoper.Monad

import Data.Void
import Control.Monad.Trans.Class

data Constraint mode modty rel = Constraint {
    constraint'judgement :: Judgement mode modty rel,
    constraint'parent :: Maybe (Constraint mode modty rel),
    constraint'reason :: String,
    constraint'id :: Int
  }

class (
    Degrees mode modty rel,
    MonadScoper mode modty rel tc
  ) => MonadTC mode modty rel tc | tc -> mode, tc -> modty, tc -> rel where
  {-| After scoping, before type-checking, metas are put to sleep.
      They awake as soon as the type-checker tries to query one.

      @'newMetaExpr'@ should only be directly used by the SCOPER.
  -}
  newMetaExpr ::
    Maybe (Constraint mode modty rel) -> rel v {-^ Degree up to which it should be solved -}
                                      -> Ctx Type mode modty v Void -> String -> tc (Term mode modty v)
  newMetaMode ::
    Maybe (Constraint mode modty rel) -> Ctx Type mode modty v Void -> String -> tc (mode v)
  newMetaModty ::
    Maybe (Constraint mode modty rel) -> Ctx Type mode modty v Void -> String -> tc (modty v)
  --term4newImplicit :: Ctx ty mode modty v Void -> tc (Term mode modty v)
  --mode4newImplicit :: Ctx ty mode modty v Void -> tc (mode v)
  --modty4newImplicit :: Ctx ty mode modty v Void -> tc (modty v)
  genVarName :: tc Raw.Name
  newConstraintID :: tc Int
  addConstraint :: Constraint mode modty rel -> tc ()
  {-| For instances. Will only be considered if all nice constraints have been considered. -}
  addConstraintReluctantly :: Constraint mode modty rel -> tc ()
  -- | Note: Avoid cyclic solutions of metas!!!
  solveMeta :: Int -> [Term mode modty v] -> Term mode modty v -> tc ()
  getMeta :: Int -> [Term mode modty v] -> tc (Maybe (Term mode modty v))
  {-| Shove a judgement aside; it will only be reconsidered when one of the given metas has been solved. -}
  blockOnMetas :: [Int] -> Constraint mode modty rel -> tc ()
  tcFail :: Constraint mode modty rel -> String -> tc ()
  leqMod :: modty v -> modty v -> tc Bool

addNewConstraint :: MonadTC mode modty rel tc =>
  Judgement mode modty rel ->
  Maybe (Constraint mode modty rel) ->
  String ->
  tc()
addNewConstraint judgement parent reason = do
  i <- newConstraintID
  addConstraint $ Constraint judgement parent reason i

-- | Not to be used by the Scoper.
newMetaTerm :: MonadTC mode modty rel tc =>
  Maybe (Constraint mode modty rel) ->
  rel v ->
  Ctx Type mode modty v Void ->
  Type mode modty v ->
  String ->
  tc (Term mode modty v)
newMetaTerm maybeParent deg gamma ty reason = do
  t <- newMetaExpr maybeParent deg gamma reason
  addNewConstraint
    (JudTerm gamma t ty)
    maybeParent
    reason
  {- --The term judgement will trigger eta-expansion.
  addNewConstraint
    (JudEta gamma t ty)
    maybeParent
    (reason ++ " (eta-expansion)")
  -}
  return t

-- | Not to be used by the Scoper.
newMetaType :: MonadTC mode modty rel tc =>
  Maybe (Constraint mode modty rel) ->
  rel v ->
  Ctx Type mode modty v Void ->
  String ->
  tc (Type mode modty v)
newMetaType maybeParent deg gamma reason = do
  t <- Type <$> newMetaExpr maybeParent deg gamma reason
  addNewConstraint
    (JudType gamma t)
    maybeParent
    reason
  return t

newMetaModedModality :: MonadTC mode modty rel tc =>
  Maybe (Constraint mode modty rel) ->
  Ctx Type mode modty v Void ->
  String ->
  tc (ModedModality mode modty v)
newMetaModedModality parent gamma reason = do
  d <- newMetaMode parent gamma reason
  mu <- newMetaModty parent gamma reason
  return $ ModedModality d mu

instance (MonadTC mode modty rel tc, MonadTrans mT, Monad (mT tc)) => MonadTC mode modty rel (mT tc) where
  newMetaExpr maybeParent deg gamma reason = lift $ newMetaExpr maybeParent deg gamma reason
  newMetaMode maybeParent gamma reason = lift $ newMetaMode maybeParent gamma reason
  newMetaModty maybeParent gamma reason = lift $ newMetaModty maybeParent gamma reason
  --term4newImplicit gamma = lift $ term4newImplicit gamma
  --mode4newImplicit gamma = lift $ mode4newImplicit gamma
  --modty4newImplicit gamma = lift $ modty4newImplicit gamma
  genVarName = lift $ genVarName
  newConstraintID = lift $ newConstraintID
  addConstraint c = lift $ addConstraint c
  addConstraintReluctantly c = lift $ addConstraintReluctantly c
  solveMeta meta depcies solution = lift $ solveMeta meta depcies solution
  getMeta meta depcies = lift $ getMeta meta depcies
  blockOnMetas metas c = lift $ blockOnMetas metas c
  tcFail c msg = lift $ tcFail c msg
  leqMod mu nu = lift $ leqMod mu nu
