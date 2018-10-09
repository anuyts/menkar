module Menkar.TCMonad.MonadTC where

import Menkar.Fine.Substitution
import Menkar.Fine.Syntax
import Menkar.Fine.Judgement
import Menkar.Fine.Context.Variable
import Menkar.Fine.Context
import qualified Menkar.Raw.Syntax as Raw
import Menkar.TCMonad.MonadScoper

data Constraint mode modty rel = Constraint {
    constraintJudgement :: Judgement mode modty rel,
    constraintParent :: Maybe (Constraint mode modty rel),
    constraintReason :: String,
    constraintID :: Int
  }

class (MonadScoper mode modty rel tc) => MonadTC mode modty rel tc | tc -> mode, tc -> modty, tc -> rel where
  newConstraintID :: tc Int
  addConstraint :: Constraint mode modty rel -> tc ()
  {-| For instances. Will only be considered if all nice constraints have been considered. -}
  addConstraintReluctantly :: Constraint mode modty rel -> tc ()
  solveMeta :: Int -> [Term mode modty v] -> Term mode modty v -> tc ()
  {-| Shove a judgement aside; it will only be reconsidered when one of the given metas has been solved. -}
  blockOnMetas :: Constraint mode modty rel -> [Int] -> tc ()
