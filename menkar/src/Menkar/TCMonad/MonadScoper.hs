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
  annot4annot :: ScCtx mode modty v Void -> 
    Raw.Qualified String -> [SmartEliminator mode modty v] -> sc (Annotation mode modty v)
  term4newImplicit :: ScCtx mode modty v Void -> sc (Term mode modty v)
  mode4newImplicit :: ScCtx mode modty v Void -> sc (mode v)
  modty4newImplicit :: ScCtx mode modty v Void -> sc (modty v)
  scopeFail :: String -> sc a

type4newImplicit :: MonadScoper mode modty rel sc =>
  ScCtx mode modty v Void -> sc (Type mode modty v)
type4newImplicit gamma = Type <$> term4newImplicit gamma

instance (MonadScoper mode modty rel sc, MonadTrans mT, Monad (mT sc)) => MonadScoper mode modty rel (mT sc) where
  annot4annot gamma qstring args = lift $ annot4annot gamma qstring args
  term4newImplicit gamma = lift $ term4newImplicit gamma
  mode4newImplicit gamma = lift $ mode4newImplicit gamma
  modty4newImplicit gamma = lift $ modty4newImplicit gamma
  scopeFail msg = lift $ scopeFail msg
