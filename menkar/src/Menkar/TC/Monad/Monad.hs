{-# LANGUAGE UndecidableInstances #-}

module Menkar.TC.Monad.Monad where

import Menkar.Fine.Syntax
import Menkar.Fine.Judgement
import Menkar.Fine.Context
import Menkar.Fine.Multimode
import qualified Menkar.Raw.Syntax as Raw

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
    Monad tc,
    Traversable mode,
    Traversable modty,
    Traversable rel
  ) => MonadTC mode modty rel tc | tc -> mode, tc -> modty, tc -> rel where
  {-| The monad remembers which metas are created by the scoper. Those metas can remain open after type-checking
      one definition. However, there should be no constraints about them!
  -}
  newMetaExpr ::
    Constraint mode modty rel -> rel v {-^ Degree up to which it should be solved -}
                              -> Ctx Type mode modty v Void -> String -> tc (Term mode modty v)
  newMetaMode ::
    Constraint mode modty rel -> Ctx Type mode modty v Void -> String -> tc (mode v)
  newMetaModty ::
    Constraint mode modty rel -> Ctx Type mode modty v Void -> String -> tc (modty v)
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

newMetaTerm :: MonadTC mode modty rel tc =>
  Constraint mode modty rel ->
  rel v ->
  Ctx Type mode modty v Void ->
  Type mode modty v ->
  String ->
  tc (Term mode modty v)
newMetaTerm parent deg gamma ty reason = do
  t <- newMetaExpr parent deg gamma reason
  addNewConstraint
    (JudTerm gamma t ty)
    (Just parent)
    reason
  addNewConstraint
    (JudEta gamma t ty)
    (Just parent)
    (reason ++ " (eta-expansion)")
  return t

newMetaType :: MonadTC mode modty rel tc =>
  Constraint mode modty rel ->
  rel v ->
  Ctx Type mode modty v Void ->
  String ->
  tc (Type mode modty v)
newMetaType parent deg gamma reason = do
  t <- Type <$> newMetaExpr parent deg gamma reason
  addNewConstraint
    (JudType gamma t)
    (Just parent)
    reason
  return t

newMetaModedModality :: MonadTC mode modty rel tc =>
  Constraint mode modty rel ->
  Ctx Type mode modty v Void ->
  String ->
  tc (ModedModality mode modty v)
newMetaModedModality parent gamma reason = do
  d <- newMetaMode parent gamma reason
  mu <- newMetaModty parent gamma reason
  return $ ModedModality d mu

instance (MonadTC mode modty rel tc, MonadTrans mT, Monad (mT tc)) => MonadTC mode modty rel (mT tc) where
  newMetaExpr parent deg gamma reason = lift $ newMetaExpr parent deg gamma reason
  newMetaMode parent gamma reason = lift $ newMetaMode parent gamma reason
  newMetaModty parent gamma reason = lift $ newMetaModty parent gamma reason
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
