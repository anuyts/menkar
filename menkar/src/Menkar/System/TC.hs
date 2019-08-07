module Menkar.System.TC where

import Menkar.System.Scoper
import Menkar.System.Fine
import Menkar.System.WHN
import Menkar.Analyzer
import Menkar.Fine
import Menkar.Monad.Monad

import Data.Void
import Data.Constraint.Witness
import Data.Functor.Const
import GHC.Generics

class SysWHN sys => SysTC sys where

  -- Judgement-checker --
  -----------------------
    
  checkSysJudgement :: forall tc .
    (MonadTC sys tc) =>
    SysJudgement sys ->
    tc ()

  -- Type-checker --
  ------------------
  
  -- | See Menkar.TC.AST.checkASTSpecial
  checkSysASTUnanalyzable :: forall tc v t .
    (MonadTC sys tc, DeBruijnLevel v, Analyzable sys t, Analyzable sys (Classif t)) =>
    SysAnalyzerError sys ->
    Ctx Type sys v Void ->
    t v ->
    ClassifExtraInput t v ->
    ClassifInfo (Classif t v) ->
    tc (Classif t v)
  -- SysTerm, Mode, Modality, Degree, SysUniHSConstructor are handled via analyzer.

  -- Relatedness-checker --
  -------------------------
  
  checkUnanalyzableSysASTRel' :: forall tc t v .
    (MonadTC sys tc, DeBruijnLevel v, Analyzable sys t) =>
    SysAnalyzerError sys ->
    Eta ->
    Relation t v ->
    Ctx (Twice2 Type) sys v Void ->
    Twice1 t v ->
    Twice1 (ClassifExtraInput t) v ->
    ClassifInfo (Twice1 (Classif t) v) ->
    tc ()
  checkMultimodeOrSysASTRel :: forall tc t v .
    (MonadTC sys tc, DeBruijnLevel v, Analyzable sys t) =>
    MultimodeOrSysAnalyzableToken sys t ->
    Eta ->
    Relation t v ->
    Ctx (Twice2 Type) sys v Void ->
    Twice1 t v ->
    Twice1 (ClassifExtraInput t) v ->
    ClassifInfo (Twice1 (Classif t) v) ->
    tc ()

  -- Eta --
  ---------

  {- | Equate an AST to its eta-expansion if it exists.
       Returns whether an eta-expansion exists, or blocks if this is unclear.
  -}
  checkEtaSys :: forall tc t v .
    (MonadTC sys tc, DeBruijnLevel v, Solvable sys t) =>
    SysAnalyzableToken sys t ->
    Ctx Type sys v Void ->
    t v ->
    ClassifExtraInput t v ->
    Classif t v ->
    tc Bool

  -- Solver --
  ------------
  
  newRelatedSysASTUnanalyzable' :: forall tc t v vOrig .
    (MonadTC sys tc, DeBruijnLevel v, DeBruijnLevel vOrig, Analyzable sys t) =>
    SysAnalyzerError sys ->
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
  newRelatedMultimodeOrSysAST :: forall tc t v vOrig .
    (MonadTC sys tc, DeBruijnLevel v, DeBruijnLevel vOrig, Analyzable sys t) =>
    MultimodeOrSysAnalyzableToken sys t ->
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

  {-| Returns an eta-expansion if eta is certainly allowed, @Just Nothing@ if it's not allowed, and @Nothing@ if unclear.
  -}
  etaExpandSysType :: forall tc v .
    (MonadTC sys tc, DeBruijnLevel v) =>
    UseHolesOrEliminees ->
    Ctx Type sys v Void ->
    Term sys v ->
    SysUniHSConstructor sys v ->
    tc (Maybe (Maybe (Term sys v)))

{--- | see Menkar.TC.Solve.checkEta.
  -- | This will generally yield false (true?), unless a system introduces types with eta via SysTerm.
  -- | ABOLISH THIS: eta isn't supported for non-universe types.
  checkEtaWHNSysTy :: forall tc v .
    (MonadTC sys tc, DeBruijnLevel v) =>
    Ctx Type sys v Void ->
    Term sys v ->
    SysTerm sys v {-^ The type -} ->
    tc Bool
-}

newMetaClassif4ast :: forall sys tc t v .
  (MonadTC sys tc,
   DeBruijnLevel v,
   SysTC sys,
   SysAnalyzer sys,
   Analyzable sys t) =>
  --AnalyzableToken sys t ->
  Ctx Type sys v Void ->
  t v ->
  ClassifExtraInput t v ->
  String ->
  tc (Classif t v)
newMetaClassif4ast gamma t extraT reason =
  haveClassif @sys @t $
  haveClassif @sys @(Classif t) $
  do
    let dgamma' = ctx'mode gamma
    let dgamma = unVarFromCtx <$> dgamma'
    ct <- newMetaClassif4astNoCheck gamma t extraT reason
    let extraCT = extraClassif @sys @t dgamma t extraT
    cct <- newMetaClassif4astNoCheck gamma ct extraCT reason
      -- It is assumed that a classifier's classifier needs no metas.
    addNewConstraint
      (Jud (analyzableToken @sys @(Classif t)) gamma ct extraCT (ClassifWillBe cct))
      reason
    return ct

newRelatedMetaMode :: forall sys tc v vOrig .
    (SysTC sys, MonadTC sys tc, DeBruijnLevel v, DeBruijnLevel vOrig) =>
    Eta ->
    Ctx Type sys vOrig Void ->
    Ctx (Twice2 Type) sys v Void ->
    (vOrig -> v) ->
    (v -> Maybe vOrig) ->
    Mode sys v ->
    String ->
    tc (Mode sys vOrig)
newRelatedMetaMode eta gammaOrig gamma subst partialInv d2 reason =
  newRelatedMultimodeOrSysAST (Left AnTokenMode) eta U1 gammaOrig gamma subst partialInv d2 U1 U1
    (ClassifWillBe $ Twice1 U1 U1) reason
