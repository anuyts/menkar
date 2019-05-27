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
  -- See Menkar.TC.AST.checkASTSpecial
  checkSysASTUnanalyzable :: forall tc v t .
    (MonadTC sys tc, DeBruijnLevel v, Analyzable sys t, Analyzable sys (Classif t)) =>
    SysAnalyzerError sys ->
    Constraint sys ->
    Ctx Type sys v Void ->
    AnalyzerError sys ->
    t v ->
    ClassifExtraInput t v ->
    ClassifInfo (Classif t v) ->
    tc (Classif t v)
  newRelatedSysASTUnanalyzable' :: forall tc t v vOrig .
    (MonadTC sys tc, DeBruijnLevel v, DeBruijnLevel vOrig, Analyzable sys t) =>
    SysAnalyzerError sys ->
    Constraint sys ->
    Relation t v ->
    Ctx Type sys vOrig Void ->
    Ctx (Twice2 Type) sys v Void ->
    (vOrig -> v) ->
    (v -> Maybe vOrig) ->
    t v ->
    ClassifExtraInput t vOrig ->
    ClassifExtraInput t v ->
    ClassifInfo (Twice1 (Classif t) v) ->
    tc (t vOrig)
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
    ClassifExtraInput t vOrig ->
    ClassifExtraInput t v ->
    ClassifInfo (Twice1 (Classif t) v) ->
    String ->
    tc (t vOrig)
  checkUnanalyzableSysASTRel' :: forall tc t v .
    (MonadTC sys tc, DeBruijnLevel v, Analyzable sys t) =>
    SysAnalyzerError sys ->
    Constraint sys ->
    Eta ->
    Relation t v ->
    Ctx (Twice2 Type) sys v Void ->
    Twice1 t v ->
    Twice1 (ClassifExtraInput t) v ->
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
    Twice1 (ClassifExtraInput t) v ->
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

  etaExpandSysType :: forall tc v .
    (MonadTC sys tc, DeBruijnLevel v) =>
    Constraint sys ->
    Ctx Type sys v Void ->
    Term sys v ->
    SysUniHSConstructor sys v ->
    tc (Maybe (Maybe (Term sys v)))
    
  checkSysJudgement :: forall tc .
    (MonadTC sys tc) =>
    Constraint sys ->
    SysJudgement sys ->
    tc ()


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
  ClassifExtraInput t v ->
  String ->
  tc (Classif t v)
newMetaClassif4ast maybeParent gamma t extraT reason =
  haveClassif @sys @t $
  haveClassif @sys @(Classif t) $
  do
    ct <- newMetaClassif4astNoCheck maybeParent gamma t extraT reason
    cct <- newMetaClassif4astNoCheck maybeParent gamma ct (extraClassif @sys @t t extraT) reason
      -- It is assumed that a classifier's classifier needs no metas.
    addNewConstraint
      (Jud (analyzableToken @sys @(Classif t)) gamma ct (extraClassif @sys @t t extraT) (ClassifWillBe cct))
      maybeParent
      reason
    return ct
