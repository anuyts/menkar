module Menkar.Fine.Judgement where

import Menkar.Fine.Syntax
import Menkar.Fine.Context
import qualified Menkar.Raw.Syntax as Raw

import Data.Void
import Control.Exception.AssertFalse
import Data.Bifunctor
import Data.Maybe
import GHC.Generics
import Data.Functor.Identity
--import Data.Functor.Compose

data Judgement (mode :: * -> *) (modty :: * -> *) (rel :: * -> *) where

  {-
  -- | @'JudType' gamma@ means @gamma |- ctx@
  JudCtx ::
    Ctx Type mode modty v Void ->
    Judgement mode modty rel
  JudCtxRel ::
    Ctx (Pair3 Type) mode modty v Void ->
    Judgement mode modty rel
  -}

  {-
  -- | @'JudMode' gamma d@ means that @d@ is a valid mode in context @gamma@.
  -- | Premises: @'JudCtx'@
  JudMode ::
    Ctx Type mode modty v Void ->
    Mode mode modty v ->
    Judgement mode modty rel
  JudModeRel ::
    Ctx (Pair3 Type) mode modty v Void ->
    Pair3 Mode mode modty v ->
    Judgement mode modty rel
  -}

  {-
  JudSegment ::
    Ctx Type mode modty v Void ->
    Segment mode modty v ->
    Judgement mode modty rel
  JudSegmentRel ::
    rel v ->
    Ctx (Pair3 Type) mode modty v Void ->
    Pair3 (Segment Type) mode modty v ->
    Judgement mode modty rel
  -}

  -- | @'JudType' gamma tyT@ means @gamma |- tyT type@
  -- | Premises: @'JudCtx'@
  JudType ::
    Ctx Type mode modty v Void ->
    Type mode modty v ->
    Judgement mode modty rel
  JudTypeRel ::
    rel v ->
    Ctx (Pair3 Type) mode modty v Void ->
    Pair3 Type mode modty v ->
    Judgement mode modty rel
    
  -- | @'JudTerm' gamma t tyT@ means @gamma |- t : tyT@.
  -- | Premises: @'JudCtx', 'JudType'@
  JudTerm ::
    Ctx Type mode modty v Void ->
    Term mode modty v ->
    Type mode modty v ->
    Judgement mode modty rel
  JudTermRel ::
    rel v ->
    Ctx (Pair3 Type) mode modty v Void ->
    Pair3 Term mode modty v ->
    Pair3 Type mode modty v ->
    Judgement mode modty rel
    
  -- | @'JudEta' gamma t tyT@ means @gamma |- t == some-eta-expansion : tyT@.
  -- | Premises: @'JudCtx', 'JudType', 'JudTerm'@
  JudEta ::
    Ctx Type mode modty v Void ->
    Term mode modty v ->
    Type mode modty v ->
    Judgement mode modty rel
    
  -- | @'JudSmartElim' gamma t tyT es r@ means @gamma |- (t : tyT) es ~> r@.
  -- | Premises: @'JudCtx gamma', 'JudType gamma tyT', 'JudTerm gamma t tyT', 'JudTerm gamma r _'@
  JudSmartElim ::
    Ctx Type mode modty v Void ->
    ModedModality mode modty v {-^ modality by which the eliminee is used -} ->
    Term mode modty v {-^ eliminee -} ->
    Type mode modty v ->
    [SmartEliminator mode modty v] {-^ eliminators -} ->
    Term mode modty v {-^ result -} ->
    Type mode modty v ->
    Judgement mode modty rel
    
  -- | @'JudGoal' gamma goalname t tyT@ means that goal @goalname@ equals term @t@.
  -- | Premises: @'JudTerm' gamma t tyT@
  JudGoal ::
    Ctx Type mode modty v Void ->
    String ->
    Term mode modty v ->
    Type mode modty v ->
    Judgement mode modty rel
    
  -- | @'JudResolve' gamma t r tyT@ means @gamma |- t ~> r : tyT@ where @t@ is a resolution call.
  -- | Premises?
  JudResolve ::
    Ctx Type mode modty v Void ->
    {- resolution call goes here -> -}
    Term mode modty v ->
    Type mode modty v ->
    Judgement mode modty rel
    
  -- JudAccuracy: "This term should be known up to that accuracy"

