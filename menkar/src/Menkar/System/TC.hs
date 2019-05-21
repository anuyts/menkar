module Menkar.System.TC where

import Menkar.System.Scoper
import Menkar.System.Fine
import Menkar.System.WHN
import Menkar.Analyzer
import Menkar.Fine
import Menkar.Monad.Monad

import Data.Void
import Data.Constraint.Witness

class SysWHN sys => SysTC sys where
  inferTermSys :: forall tc v .
    (MonadTC sys tc, DeBruijnLevel v) =>
    Constraint sys ->
    Ctx Type sys v Void ->
    SysTerm sys v ->
    tc (Type sys v)
  checkTermSys :: forall tc v .
    (MonadTC sys tc, DeBruijnLevel v) =>
    Constraint sys ->
    Ctx Type sys v Void ->
    SysTerm sys v ->
    Type sys v ->
    tc ()
  -- see Menkar.TC.Solve.solveMetaAgainstWHNF
  newRelatedSysTerm :: forall tc v vOrig .
    (MonadTC sys tc, Eq v, DeBruijnLevel v, DeBruijnLevel vOrig) =>
    Constraint sys ->
    ModedDegree sys v ->
    Ctx Type sys vOrig Void ->
    Ctx (Twice2 Type) sys v Void ->
    (vOrig -> v) ->
    (v -> Maybe vOrig) ->
    SysTerm sys v ->
    Type sys v ->
    Type sys v ->
    (String -> tc ()) ->
    tc (Maybe (Term sys vOrig))
  -- see Menkar.TC.Rel
  {-
  checkTermRelSysTermWHNTerm :: forall tc v .
    (MonadTC sys tc, DeBruijnLevel v) =>
    Constraint sys ->
    Eta ->
    ModedDegree sys v ->
    Ctx (Twice2 Type) sys v Void ->
    SysTerm sys v ->
    Term sys v ->
    Type sys v ->
    Type sys v ->
    [Int] ->
    [Int] ->
    tc ()
  -}
  checkUnanalyzableSysASTRel :: forall tc t v .
    (MonadTC sys tc, DeBruijnLevel v, Analyzable sys t) =>
    SysAnalyzerError sys ->
    Constraint sys ->
    Eta ->
    Relation t v ->
    Ctx (Twice2 Type) sys v Void ->
    t v ->
    t v ->
    ClassifInfo (Twice1 (Classif t) v) ->
    tc ()
  checkSysASTRel :: forall tc t v .
    (MonadTC sys tc, DeBruijnLevel v, Analyzable sys t) =>
    SysAnalyzableToken sys t ->
    Constraint sys ->
    Eta ->
    Relation t v ->
    Ctx (Twice2 Type) sys v Void ->
    Twice1 t v ->
    Twice1 (AnalyzerExtraInput t) v ->
    ClassifInfo (Twice1 (Classif t) v) ->
    tc ()
  -- | see Menkar.TC.Solve.checkEta.
  -- | This will generally yield false (true?), unless a system introduces types with eta via SysTerm.
  -- | ABOLISH THIS: eta isn't supported for non-universe types.
  checkEtaWHNSysTy :: forall tc v .
    (MonadTC sys tc, DeBruijnLevel v) =>
    Constraint sys ->
    Ctx Type sys v Void ->
    Term sys v ->
    SysTerm sys v {-^ The type -} ->
    tc Bool

  checkSysUniHSConstructor :: forall tc v .
    (MonadTC sys tc, DeBruijnLevel v) =>
    Constraint sys ->
    Ctx Type sys v Void ->
    SysUniHSConstructor sys v ->
    Type sys v ->
    tc ()
  -- | See Menkar.TC.Solve
  newRelatedSysUniHSConstructor :: forall tc v vOrig .
    (MonadTC sys tc, Eq v, DeBruijnLevel v, DeBruijnLevel vOrig) =>
    Constraint sys ->
    ModedDegree sys v ->
    Ctx Type sys vOrig Void ->
    Ctx (Twice2 Type) sys v Void ->
    (vOrig -> v) ->
    (v -> Maybe vOrig) ->
    SysUniHSConstructor sys v ->
    tc (SysUniHSConstructor sys vOrig)
  etaExpandSysType :: forall tc v .
    (MonadTC sys tc, DeBruijnLevel v) =>
    Constraint sys ->
    Ctx Type sys v Void ->
    Term sys v ->
    SysUniHSConstructor sys v ->
    tc (Maybe (Maybe (Term sys v)))
  checkSysUniHSConstructorRel :: forall tc v .
    (MonadTC sys tc, DeBruijnLevel v) =>
    Constraint sys ->
    ModedDegree sys v ->
    Ctx (Twice2 Type) sys v Void ->
    SysUniHSConstructor sys v ->
    SysUniHSConstructor sys v ->
    Type sys v ->
    Type sys v ->
    [Int] ->
    [Int] ->
    tc ()
    
  -- | Check @'JudMode'@.
  checkMode :: forall tc v .
    (MonadTC sys tc, DeBruijnLevel v) =>
    Constraint sys ->
    Ctx Type sys v Void ->
    Mode sys v ->
    tc ()
  -- | Check @'JudModeRel'@.
  checkModeRel :: forall tc v .
    (MonadTC sys tc, DeBruijnLevel v) =>
    Constraint sys ->
    Ctx (Twice2 Type) sys v Void ->
    Mode sys v ->
    Mode sys v ->
    tc ()
  checkModality :: forall tc v .
    (MonadTC sys tc, DeBruijnLevel v) =>
    Constraint sys ->
    Ctx Type sys v Void ->
    Modality sys v ->
    Mode sys v ->
    Mode sys v ->
    tc ()
  checkModalityRel :: forall tc v .
    (MonadTC sys tc, DeBruijnLevel v) =>
    Constraint sys ->
    ModRel ->
    Ctx (Twice2 Type) sys v Void ->
    Modality sys v ->
    Modality sys v ->
    Mode sys v ->
    Mode sys v ->
    tc ()
  checkSysJudgement :: forall tc .
    (MonadTC sys tc) =>
    Constraint sys ->
    SysJudgement sys ->
    tc ()

  -- | See Menkar.TC.ASTRel.newRelatedAST
  newRelatedSysAST :: forall tc t v vOrig .
    (MonadTC sys tc, DeBruijnLevel v, DeBruijnLevel vOrig, Analyzable sys t) =>
    SysAnalyzableToken sys t ->
    Constraint sys ->
    Eta ->
    Relation t v ->
    Ctx Type sys vOrig Void ->
    Ctx (Twice2 Type) sys v Void ->
    (vOrig -> v) ->
    (v -> Maybe vOrig) ->
    t v ->
    Twice1 (AnalyzerExtraInput t) v ->
    ClassifInfo (Twice1 (Classif t) v) ->
    (String -> tc ()) ->
    String ->
    tc (Maybe (t vOrig))

newMetaClassif4ast :: forall sys tc t v .
  (MonadTC sys tc,
   DeBruijnLevel v,
   SysTC sys,
   SysAnalyzer sys,
   Analyzable sys t) =>
  --AnalyzableToken sys t ->
  Maybe (Constraint sys) ->
  Ctx Type sys v Void ->
  t v ->
  AnalyzerExtraInput t v ->
  String ->
  tc (Classif t v)
newMetaClassif4ast maybeParent gamma t extraT reason =
  haveClassif @sys @t $
  haveClassif @sys @(Classif t) $
  do
    ct <- newMetaClassif4astNoCheck maybeParent gamma t extraT reason
    cct <- newMetaClassif4astNoCheck maybeParent gamma ct (extraClassif @sys @t) reason
      -- It is assumed that a classifier's classifier needs no metas.
    addNewConstraint
      (Jud (analyzableToken @sys @(Classif t)) gamma ct (extraClassif @sys @t) (ClassifWillBe cct))
      maybeParent
      reason
    return ct
