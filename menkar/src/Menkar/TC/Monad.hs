module Menkar.TC.Monad where

import Menkar.Fine.Syntax
import Menkar.Fine.Judgement
import Menkar.Fine.Context
import Menkar.Fine.Multimode
import qualified Menkar.Raw.Syntax as Raw
import Data.Void

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
  term4newImplicit :: Ctx ty mode modty v Void -> tc (Term mode modty v)
  mode4newImplicit :: Ctx ty mode modty v Void -> tc (mode v)
  modty4newImplicit :: Ctx ty mode modty v Void -> tc (modty v)
  genVarName :: tc Raw.Name
  newConstraintID :: tc Int
  addConstraint :: Constraint mode modty rel -> tc ()
  {-| For instances. Will only be considered if all nice constraints have been considered. -}
  addConstraintReluctantly :: Constraint mode modty rel -> tc ()
  solveMeta :: Int -> [Term mode modty v] -> Term mode modty v -> tc ()
  {-| Shove a judgement aside; it will only be reconsidered when one of the given metas has been solved. -}
  blockOnMetas :: [Int] -> Constraint mode modty rel -> tc ()
  tcFail :: Constraint mode modty rel -> String -> tc ()
  leqMod :: modty v -> modty v -> tc Bool
