{-# LANGUAGE UndecidableInstances #-}

module Menkar.TCMonad.MonadScoper where

import Menkar.Fine.Substitution
import Menkar.Fine.Syntax
import Menkar.Fine.Judgement
import Menkar.Fine.Context.Variable
import Menkar.Fine.Context
import qualified Menkar.Raw.Syntax as Raw
import Control.Monad.State.Lazy
import Data.Void

data Constraint mode modty rel = Constraint {
    constraintJudgement :: Judgement mode modty rel,
    constraintParent :: Maybe (Constraint mode modty rel),
    constraintReason :: String
  }

class (
    Monad sc,
    Traversable mode,
    Traversable modty,
    Traversable rel
  ) => MonadScoper
    (mode :: * -> *)
    (modty :: * -> *)
    (rel :: * -> *)
    (sc :: * -> *)
    | sc -> mode, sc -> modty, sc -> rel where
    -- -| mode -> modty, mode -> rel where
  --type ConstraintRef sc :: *
  term4val :: Ctx Type mode modty v Void -> mode v -> Raw.QName -> sc (Term mode modty v)
  annot4annot :: Ctx Type mode modty v Void -> mode v ->
    Raw.Qualified String -> [Term mode modty v] -> sc (Annotation mode modty v)
  {- TODO: also return an implicit-ref -}
  term4newImplicit :: Ctx Type mode modty v Void -> mode v -> sc (Term mode modty v)
  type4newImplicit :: Ctx Type mode modty v Void -> mode v -> sc (Type mode modty v)
  mode4newImplicit :: Ctx Type mode modty v Void -> mode v -> sc (mode v)
  modty4newImplicit :: Ctx Type mode modty v Void -> mode v -> sc (modty v)
  --newModule :: Ctx Type mode modty v Void -> mode v -> Maybe String ->
  pushConstraint :: Constraint mode modty rel -> sc ()
  scopeFail :: String -> sc a

instance (MonadScoper mode modty rel sc, MonadTrans mT, Monad (mT sc)) => MonadScoper mode modty rel (mT sc) where
  term4val gamma d qname = lift $ term4val gamma d qname
  annot4annot gamma d qstring args = lift $ annot4annot gamma d qstring args
  term4newImplicit gamma d = lift $ term4newImplicit gamma d
  type4newImplicit gamma d = lift $ type4newImplicit gamma d
  mode4newImplicit gamma d = lift $ mode4newImplicit gamma d
  modty4newImplicit gamma d = lift $ modty4newImplicit gamma d
  pushConstraint c = lift $ pushConstraint c
  scopeFail msg = lift $ scopeFail msg
