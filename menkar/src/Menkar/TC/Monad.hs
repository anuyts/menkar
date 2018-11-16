{-# LANGUAGE UndecidableInstances #-}

module Menkar.TC.Monad where

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
  term4newImplicit :: Ctx ty mode modty v Void -> tc (Term mode modty v)
  mode4newImplicit :: Ctx ty mode modty v Void -> tc (mode v)
  modty4newImplicit :: Ctx ty mode modty v Void -> tc (modty v)
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

modedModality4newImplicit :: MonadTC mode modty rel tc => Ctx ty mode modty v Void -> tc (ModedModality mode modty v)
modedModality4newImplicit gamma = do
  d <- mode4newImplicit gamma
  mu <- modty4newImplicit gamma
  return $ ModedModality d mu

instance (MonadTC mode modty rel tc, MonadTrans mT, Monad (mT tc)) => MonadTC mode modty rel (mT tc) where
  term4newImplicit gamma = lift $ term4newImplicit gamma
  mode4newImplicit gamma = lift $ mode4newImplicit gamma
  modty4newImplicit gamma = lift $ modty4newImplicit gamma
  genVarName = lift $ genVarName
  newConstraintID = lift $ newConstraintID
  addConstraint c = lift $ addConstraint c
  addConstraintReluctantly c = lift $ addConstraintReluctantly c
  solveMeta meta depcies solution = lift $ solveMeta meta depcies solution
  getMeta meta depcies = lift $ getMeta meta depcies
  blockOnMetas metas c = lift $ blockOnMetas metas c
  tcFail c msg = lift $ tcFail c msg
  leqMod mu nu = lift $ leqMod mu nu
