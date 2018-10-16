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

  {-
  -- | @'JudType' gamma d@ means @gamma |-{d} ctx@
  JudCtx ::
    Ctx Type mode modty v Void ->
    mode v ->
    Judgement mode modty rel
  JudCtxRel ::
    Ctx (Pair3 Type) mode modty v Void ->
    mode v ->
    Judgement mode modty rel
  -}
  
  -- | @'JudType' gamma d tyT@ means @gamma |-{d} tyT type@
  -- | Premises: @'JudCtx'@
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
  
  -- | @'JudValSpec' gamma d (delta :|- tyT)@ means @gamma . delta |-{d} ctx@ and @gamma . delta |-{d} tyT type@.
  -- | Premises: @'JudCtx' gamma d@
  JudValSpec ::
    Ctx Type mode modty v Void ->
    mode v ->
    ValSpec mode modty v ->
    Judgement mode modty rel
  JudValSpecRel ::
    rel v ->
    Ctx (Pair3 Type) mode modty v Void ->
    mode v ->
    Pair3 ValSpec mode modty v ->
    Judgement mode modty rel
    
  -- | @'JudTerm' gamma d t tyT@ means @gamma |-{d} t : tyT@.
  -- | Premises: @'JudCtx', 'JudType'@
  JudTerm ::
    Ctx Type mode modty v Void ->
    mode v ->
    Term mode modty v ->
    Type mode modty v ->
    Judgement mode modty rel
  JudTermRel ::
    rel v ->
    Ctx (Pair3 Type) mode modty v Void ->
    mode v ->
    Pair3 Term mode modty v ->
    Pair3 Type mode modty v ->
    Judgement mode modty rel
    
  -- | @'JudPseudoTerm' gamma d t (delta :|- tyT)@ means @gamma . delta |-{d} t delta : tyT@.
  -- | Premises: @'JudCtx', 'JudType'@
  JudPseudoTerm ::
    Ctx Type mode modty v Void ->
    mode v ->
    Term mode modty v ->
    ValSpec mode modty v ->
    Judgement mode modty rel
  JudPseudoTermRel ::
    rel v ->
    Ctx (Pair3 Type) mode modty v Void ->
    mode v ->
    Pair3 Term mode modty v ->
    Pair3 ValSpec mode modty v ->
    Judgement mode modty rel
    
  -- | @'JudEta' gamma d t tyT@ means @gamma |-{d} t == some-eta-expansion : tyT@.
  -- | Premises: @'JudCtx', 'JudType', 'JudTerm'@
  JudEta ::
    Ctx Type mode modty v Void ->
    mode v -> 
    Term mode modty v ->
    Type mode modty v ->
    Judgement mode modty rel
    
  -- | @'JudSmartElim' gamma d t tyT es r@ means @gamma |-{d} (t : tyT) es ~> r@.
  -- | Premises: @'JudCtx gamma d', 'JudType gamma d tyT', 'JudTerm gamma d t tyT', 'JudTerm gamma d r _'@
  JudSmartElim ::
    Ctx Type mode modty v Void ->
    mode v -> 
    Term mode modty v ->
    Type mode modty v ->
    [SmartEliminator mode modty v] ->
    Term mode modty v ->
    Judgement mode modty rel
    
  -- | @'JudGoal' gamma d goalname t tyT@ means that goal @goalname@ equals term @t@.
  -- | Premises: @'JudTerm'@
  JudGoal ::
    Ctx Type mode modty v Void ->
    mode v -> 
    String ->
    Term mode modty v ->
    Type mode modty v ->
    Judgement mode modty rel
    
  -- | @'JudResolve' gamma d t r tyT@ means @gamma |-{d} t ~> r : tyT@ where @t@ is a resolution call.
  -- | Premises?
  JudResolve ::
    Ctx Type mode modty v Void ->
    mode v ->
    {- resolution call goes here -> -}
    Term mode modty v ->
    Type mode modty v ->
    Judgement mode modty rel
    
  -- JudAccuracy: "This term should be known up to that accuracy"

