module Menkar.Fine.Judgement where

import Menkar.System.Fine
import Menkar.Fine.Syntax
import Menkar.Fine.Context
import qualified Menkar.Raw.Syntax as Raw

import Data.Void
import Control.Exception.AssertFalse
import Data.Bifunctor
import Data.Maybe
import GHC.Generics
import Data.Functor.Identity
import Data.Kind hiding (Type)
--import Data.Functor.Compose

data ModRel = ModEq | ModLeq

data Judgement (sys :: KSys) where

  {-
  -- | @'JudType' gamma@ means @gamma |- ctx@
  JudCtx ::
    Ctx Type sys v Void ->
    Judgement sys
  JudCtxRel ::
    Ctx (Twice2 Type) sys v Void ->
    Judgement sys
  -}

  {-
  -- | @'JudMode' gamma d@ means that @d@ is a valid mode in context @gamma@.
  -- | Premises: @'JudCtx'@
  JudMode ::
    Ctx Type sys v Void ->
    Mode sys v ->
    Judgement sys
  JudModeRel ::
    Ctx (Twice2 Type) sys v Void ->
    Twice2 Mode sys v ->
    Judgement sys
  -}

  {-
  JudSegment ::
    Ctx Type sys v Void ->
    Segment sys v ->
    Judgement sys
  JudSegmentRel ::
    rel v ->
    Ctx (Twice2 Type) sys v Void ->
    Twice2 (Segment Type) sys v ->
    Judgement sys
  -}

  -- | @'JudType' gamma tyT@ means @gamma |- tyT type@
  -- | Premises: @'JudCtx'@
  JudType :: (DeBruijnLevel v) =>
    Ctx Type sys v Void ->
    Type sys v ->
    Judgement sys
  JudTypeRel :: (DeBruijnLevel v) =>
    Degree sys v ->
    Ctx (Twice2 Type) sys v Void ->
    Twice2 Type sys v ->
    Judgement sys
    
  -- | @'JudTerm' gamma t tyT@ means @gamma |- t : tyT@.
  -- | Premises: @'JudCtx', 'JudType'@
  JudTerm :: (DeBruijnLevel v) =>
    Ctx Type sys v Void ->
    Term sys v ->
    Type sys v ->
    Judgement sys
  JudTermRel :: (DeBruijnLevel v) =>
    Degree sys v ->
    Ctx (Twice2 Type) sys v Void ->
    Twice2 Term sys v ->
    Twice2 Type sys v ->
    Judgement sys
    
  -- | @'JudEta' gamma t tyT@ means @gamma |- t == some-eta-expansion : tyT@.
  -- | Premises: @'JudCtx', 'JudType', 'JudTerm'@
  JudEta :: (DeBruijnLevel v) =>
    Ctx Type sys v Void ->
    Term sys v ->
    Type sys v ->
    Judgement sys
    
  -- | @'JudSmartElim' gamma t tyT es r@ means @gamma |- (t : tyT) es ~> r@.
  -- | Premises: @'JudCtx gamma', 'JudType gamma tyT', 'JudTerm gamma t tyT', 'JudTerm gamma r _'@
  JudSmartElim :: (DeBruijnLevel v) =>
    Ctx Type sys v Void ->
    Term sys v {-^ eliminee -} ->
    Type sys v ->
    [Pair2 ModedModality SmartEliminator sys v] {-^ eliminators -} ->
    Term sys v {-^ result -} ->
    Type sys v ->
    Judgement sys
    
  -- | @'JudGoal' gamma goalname t tyT@ means that goal @goalname@ equals term @t@.
  -- | Premises: @'JudTerm' gamma t tyT@
  JudGoal :: (DeBruijnLevel v) =>
    Ctx Type sys v Void ->
    String ->
    Term sys v ->
    Type sys v ->
    Judgement sys
    
  -- | @'JudResolve' gamma t r tyT@ means @gamma |- t ~> r : tyT@ where @t@ is a resolution call.
  -- | Premises?
  JudResolve :: (DeBruijnLevel v) =>
    Ctx Type sys v Void ->
    {- resolution call goes here -> -}
    Term sys v ->
    Type sys v ->
    Judgement sys
    
  JudMode :: (DeBruijnLevel v) =>
    Ctx Type sys v Void ->
    Mode sys v ->
    Judgement sys
  JudModeRel :: (DeBruijnLevel v) =>
    Ctx (Twice2 Type) sys v Void ->
    Mode sys v ->
    Mode sys v ->
    Judgement sys

  JudModality :: (DeBruijnLevel v) =>
    Ctx Type sys v Void ->
    Modality sys v ->
    Mode sys v ->
    Mode sys v ->
    Judgement sys
  JudModalityRel :: (DeBruijnLevel v) =>
    ModRel ->
    Ctx (Twice2 Type) sys v Void ->
    Modality sys v ->
    Modality sys v ->
    Mode sys v ->
    Mode sys v ->
    Judgement sys

  JudSys :: SysJudgement sys -> Judgement sys

  ------------------------------

  JudSegment :: (DeBruijnLevel v) =>
    Ctx Type sys v Void ->
    Segment Type sys v ->
    Judgement sys

  JudVal :: (DeBruijnLevel v) =>
    Ctx Type sys v Void ->
    Val sys v ->
    Judgement sys

  JudModule :: (DeBruijnLevel v) =>
    Ctx Type sys v Void ->
    Module sys v ->
    Judgement sys

  JudEntry :: (DeBruijnLevel v) =>
    Ctx Type sys v Void ->
    Entry sys v ->
    Judgement sys
