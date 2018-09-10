module Menkar.Fine.Judgement where

import Menkar.Fine.Substitution
import Menkar.Fine.Syntax
import Menkar.Fine.Context
import Data.Void
import Control.Exception.AssertFalse
import qualified Menkar.Raw.Syntax as Raw
import Data.Bifunctor
import Data.Maybe
import GHC.Generics
import Data.Functor.Identity
--import Data.Functor.Compose

data Judgement (mode :: * -> *) (modty :: * -> *) (rel :: * -> *) where
  -- | @'JudType' gamma d tyT@ means @gamma |-{d} tyT type@
  JudType ::
    Ctx Type mode modty v Void ->
    mode v ->
    Type mode modty v ->
    Judgement mode modty rel
  JudTypeRel ::
    rel v ->
    Ctx (Pair3 Type) mode modty v Void ->
    mode v ->
    Pair3 Type mode modty v ->
    Judgement mode modty rel
  -- | @'JudTyping' gamma d t tyT@ means @gamma |-{d} t : tyT@.
  JudTyping ::
    Ctx Type mode modty v Void ->
    mode v ->
    Term mode modty v ->
    Type mode modty v ->
    Judgement mode modty rel
  JudTypingRel ::
    rel v ->
    Ctx (Pair3 Type) mode modty v Void ->
    mode v ->
    (Term mode modty v, Term mode modty v) ->
    Pair3 Type mode modty v ->
    Judgement mode modty rel
  -- | @'JudEta' gamma d t tyT@ means @gamma |-{d} t == some-eta-expansion : tyT@.
  JudEta ::
    Ctx Type mode modty v Void ->
    mode v -> 
    Term mode modty v ->
    Type mode modty v ->
    Judgement mode modty rel
  -- | @'JudSmartElim' gamma d t tyT es r@ means @gamma |-{d} (t : tyT) es ~> r@.
  JudSmartElim ::
    Ctx Type mode modty v Void ->
    mode v -> 
    Term mode modty v ->
    Type mode modty v ->
    [SmartEliminator mode modty v] ->
    Term mode modty v ->
    Judgement mode modty rel
  -- | @'JudResolve' gamma d t r tyT@ means @gamma |-{d} t ~> r : tyT@ where @t@ is a resolution call.
  JudResolve ::
    Ctx Type mode modty v Void ->
    mode v ->
    {- resolution call goes here -> -}
    Term mode modty v ->
    Type mode modty v ->
    Judgement mode modty rel
  -- JudAccuracy: "This term should be known up to that accuracy"
  -- JudReport: "This term is that goal and should be reported on" (maybe this is not a judgement, but something in the monad).

-------------------------------------------------------------

{-
peelTelescoped ::
  Ctx ty mode modty v ->
  Telescoped ty rhs mode modty v ->
  (forall w . (v -> w) -> Ctx ty mode modty w -> rhs mode modty w -> motive) ->
  motive
peelTelescoped gamma (Telescoped rhs) k = k id gamma rhs
peelTelescoped gamma (seg :|- thing) k =
  peelTelescoped (gamma :.. seg) thing (\ wkn' -> k (wkn' . Just))
-}
