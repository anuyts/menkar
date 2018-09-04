module Menkar.TCMonad.MonadScoper where

import Menkar.Fine.Substitution
import Menkar.Fine.Syntax
import Menkar.Fine.Judgement
import qualified Menkar.Raw.Syntax as Raw

data Constraint mode modty rel = Constraint {
    constraintJudgement :: Judgement mode modty rel,
    constraintParent :: Maybe (Constraint mode modty rel),
    constraintReason :: String
  }

class Monad sc => MonadScoper
    (mode :: * -> *)
    (modty :: * -> *)
    (rel :: * -> *)
    (sc :: * -> *)
    | mode -> modty, mode -> rel where
  --type ConstraintRef sc :: *
  term4val :: Ctx Type mode modty v -> Raw.QName -> sc (Term mode modty v)
  {- TODO: also return an implicit-ref -}
  term4newImplicit :: Ctx Type mode modty v -> sc (Term mode modty v)
  type4newImplicit :: Ctx Type mode modty v -> sc (Type mode modty v)
  --mode4newImplicit :: Ctx Type mode modty v -> sc (mode v)
  pushConstraint :: Constraint mode modty rel -> sc ()
