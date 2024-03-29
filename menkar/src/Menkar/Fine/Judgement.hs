module Menkar.Fine.Judgement where

import Menkar.System.Fine
import Menkar.Fine.Syntax
import Menkar.Fine.Context
import qualified Menkar.Raw.Syntax as Raw
import Menkar.Analyzer.Class
import Menkar.Analyzer.Syntax
import Menkar.ID

import Data.Functor.Coyoneda.NF
import Control.DeepSeq.Redone

import Data.Void
import Control.Exception.AssertFalse
import Data.Bifunctor
import Data.Maybe
import GHC.Generics
import Data.Functor.Identity
import Data.Kind hiding (Type)
--import Data.Functor.Compose

newtype Eta = Eta {unEta :: Bool} deriving newtype NFData

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

  -- Quantified class constraints `SysAnalyzer sys => Analyzable sys t` would be more appropriate here.
  Jud :: (DeBruijnLevel v, Analyzable sys t, Analyzable sys (Classif t)) =>
    AnalyzableToken sys t ->
    Ctx Type sys v ->
    t v ->
    ClassifExtraInput t v ->
    ClassifInfo (Classif t v) {-^ Unknown not allowed for AnalyzerError cases. -} ->
    Judgement sys
  JudRel :: (DeBruijnLevel v, Analyzable sys t) =>
    AnalyzableToken sys t ->
    Eta ->
    Coyoneda (Relation t) v ->
    Ctx (Twice2 Type) sys v ->
    Twice1 t v ->
    Twice1 (ClassifExtraInput t) v ->
    ClassifInfo (Twice1 (Classif t) v) {-^ Will or unknown; not must. Unknown not allowed for terms. -} ->
    Judgement sys
    
  -- | @'JudEta' gamma t tyT@ means @gamma |- t == some-eta-expansion : tyT@.
  -- | Premises: @'JudCtx', 'JudType', 'JudTerm'@
  -- | Only allowed for meta terms.
  JudEta :: (DeBruijnLevel v, Solvable sys t) =>
    AnalyzableToken sys t {-^ It would be cleaner to have a SolvableToken here. -} ->
    Ctx Type sys v ->
    t v ->
    ClassifExtraInput t v ->
    Classif t v ->
    Judgement sys
    
  -- | @'JudSmartElim' gamma t tyT es r@ means @gamma |- (t : tyT) es ~> r@.
  -- | Premises: @'JudCtx gamma', 'JudType gamma tyT', 'JudTerm gamma t tyT', 'JudTerm gamma r _'@
  JudSmartElim :: (DeBruijnLevel v) =>
    Ctx Type sys v ->
    Term sys v {-^ eliminee -} ->
    Type sys v ->
    [(ModedModality sys :*: SmartEliminator sys) v] {-^ eliminators -} ->
    Term sys v {-^ result -} ->
    Type sys v ->
    Judgement sys
    
  -- | @'JudGoal' gamma goalname t tyT@ means that goal @goalname@ equals term @t@.
  -- | Premises: @'JudTerm' gamma t tyT@
  JudGoal :: (DeBruijnLevel v) =>
    Ctx Type sys v ->
    String ->
    Term sys v ->
    Type sys v ->
    Judgement sys
    
  -- | @'JudResolve' gamma t r tyT@ means @gamma |- t ~> r : tyT@ where @t@ is a resolution call.
  -- | Premises?
  JudResolve :: (DeBruijnLevel v) =>
    Ctx Type sys v ->
    {- resolution call goes here -> -}
    Term sys v ->
    Type sys v ->
    Judgement sys

{-
  -- | Checking is immediately delegated to the system.
  JudMode :: (DeBruijnLevel v) =>
    Ctx Type sys v Void ->
    Mode sys v ->
    Judgement sys
  -- | Checking is immediately delegated to the system.
  JudModeRel :: (DeBruijnLevel v) =>
    Ctx (Twice2 Type) sys v Void ->
    Mode sys v ->
    Mode sys v ->
    Judgement sys

  -- | Checking is immediately delegated to the system.
  JudModality :: (DeBruijnLevel v) =>
    Ctx Type sys v Void ->
    Modality sys v ->
    Mode sys v ->
    Mode sys v ->
    Judgement sys
  -- | Checking is immediately delegated to the system.
  JudModalityRel :: (DeBruijnLevel v) =>
    ModRel ->
    Ctx (Twice2 Type) sys v Void ->
    Modality sys v ->
    Modality sys v ->
    Mode sys v ->
    Mode sys v ->
    Judgement sys

  JudModedModality :: (DeBruijnLevel v) =>
    Ctx Type sys v Void ->
    ModedModality sys v ->
    Mode sys v ->
    Judgement sys
  JudModedModalityRel :: (DeBruijnLevel v) =>
    ModRel ->
    Ctx (Twice2 Type) sys v Void ->
    ModedModality sys v ->
    ModedModality sys v ->
    Mode sys v ->
    Judgement sys
-}

  -- | Checking is immediately delegated to the system.
  JudSys :: SysJudgement sys -> Judgement sys

  ------------------------------

{-
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
-}

{-
  JudBlock ::
    [(Int {- all metas blocking this thing -}, String {- Reason for requesting those metas -})] ->
    String {-^ Reason for blocking -} ->
    Judgement sys

  JudUnblock ::
    Int {-^ Meta that caused the unblocking. -} ->
    Judgement sys
-}

  JudBlock :: WorryID -> Judgement sys
  JudUnblock :: WorryID -> Judgement sys

instance SysTrav sys => NFData (Judgement sys) where
  rnf (Jud token gamma t extraT ct) =
    rnf gamma `seq` rnf_ t `seq` rnf_ extraT `seq` rnf_ ct
  rnf (JudRel token eta rel gamma ts extraTs cts) =
    rnf eta `seq` rnf_ rel `seq` rnf gamma `seq` rnf_ ts `seq` rnf_ extraTs `seq` rnf_ cts
  rnf (JudEta token gamma t extraT ct) =
    rnf gamma `seq` rnf_ t `seq` rnf_ extraT `seq` rnf_ ct
  rnf (JudSmartElim gamma tEliminee tyEliminee eliminators tResult tyResult) =
    rnf gamma `seq` rnf_ tEliminee `seq` rnf_ tyEliminee `seq` liftRnf rnf_ eliminators `seq` rnf_ tResult `seq` rnf_ tyResult
  rnf (JudGoal gamma str t ty) =
    rnf gamma `seq` rnf str `seq` rnf_ t `seq` rnf_ ty
  rnf (JudResolve gamma t ty) = todo
  rnf (JudSys sysJud) = rnf sysJud
  rnf (JudBlock iD) = rnf iD
  rnf (JudUnblock iD) = rnf iD

-- | @'JudType' gamma tyT@ means @gamma |- tyT type@
-- | Premises: @'JudCtx'@
{-JudType :: (DeBruijnLevel v) =>
    Ctx Type sys v Void ->
    Type sys v ->
    Judgement sys-}
pattern JudType gamma ty = Jud AnTokenType gamma ty U1 (ClassifWillBe U1)
{-JudTypeRel :: (DeBruijnLevel v) =>
    Degree sys v ->
    Ctx (Twice2 Type) sys v Void ->
    Twice2 Type sys v ->
    Judgement sys-}
pattern JudTypeRel deg gamma tys
  <- JudRel AnTokenType _ deg gamma (twice1to2 -> tys) (Twice1 U1 U1) (ClassifWillBe (Twice1 U1 U1))
  where JudTypeRel deg gamma (Twice2 ty1 ty2) =
          JudRel AnTokenType (Eta False) deg gamma (Twice1 ty1 ty2) (Twice1 U1 U1) (ClassifWillBe (Twice1 U1 U1))
    
-- | @'JudTerm' gamma t tyT@ means @gamma |- t : tyT@.
-- | Premises: @'JudCtx', 'JudType'@
{-JudTerm :: (DeBruijnLevel v) =>
    Ctx Type sys v Void ->
    Term sys v ->
    Type sys v ->
    Judgement sys-}
pattern JudTerm gamma t ty = Jud AnTokenTerm gamma t U1 (ClassifMustBe ty)
{-JudTermRel :: (DeBruijnLevel v) =>
    Eta ->
    Degree sys v ->
    Ctx (Twice2 Type) sys v Void ->
    Twice2 Term sys v ->
    Twice2 Type sys v ->
    Judgement sys-}
pattern JudTermRel eta deg gamma ts tys
  <- JudRel AnTokenTerm eta deg gamma (twice1to2 -> ts) (Twice1 U1 U1) (fmap twice1to2 -> ClassifMustBe tys)
  where JudTermRel eta deg gamma (Twice2 t1 t2) (Twice2 ty1 ty2)
          = JudRel AnTokenTerm eta deg gamma (Twice1 t1 t2) (Twice1 U1 U1) (ClassifWillBe (Twice1 ty1 ty2))
