module Menkar.TC.ASTRel where

import Menkar.System.Fine
import Menkar.Fine
import Menkar.Analyzer
import Menkar.WHN
import Menkar.System.TC
import Menkar.Basic.Context
import Menkar.Monad
import Menkar.TC.QuickEq
import Menkar.TC.ASTSolve

import Control.Exception.AssertFalse
import Data.Constraint.Conditional

import Data.Void
import Control.Lens
import Data.Functor.Compose
import Control.Monad
import Control.Monad.Writer.Lazy
import GHC.Generics
import Data.Maybe

---------------------------------------------------

checkASTRel' :: forall sys tc t v .
  (SysTC sys, MonadTC sys tc, DeBruijnLevel v, Analyzable sys t) =>
  Eta ->
  Relation t v ->
  Ctx (Twice2 Type) sys v Void ->
  Twice1 t v ->
  Twice1 (ClassifExtraInput t) v ->
  ClassifInfo (Twice1 (Classif t) v) ->
  tc ()
checkASTRel' eta relT gamma (Twice1 t1 t2) (Twice1 extraT1 extraT2) maybeCTs = do
  let maybeCT1 = fstTwice1 <$> maybeCTs
  let maybeCT2 = sndTwice1 <$> maybeCTs
  let inputT1 = (Classification t1 extraT1 maybeCT1)
  let inputT2 = (Classification t2 extraT2 maybeCT2)
  attempt <- sequenceA $ analyze TokenRel gamma inputT1
    $ \ wkn _ extract extCtx extractRel addressInfo ->
      case (extract gamma inputT1, extract gamma inputT2) of
        (Nothing, _) -> unreachable
        (Just _, Nothing) -> tcFail  "False"
        (Just (Classification (s1 :: s _) extraS1 maybeCS1),
         Just (Classification (s2 :: s _) extraS2 maybeCS2)) -> do
          let relS = extractRel (unVarFromCtx <$> ctx'mode gamma) relT
          let gammadelta = fromMaybe unreachable $ extCtx TokenTrue gamma inputT1 (conditional inputT2)
              -- Cannot fail because we already know that the shapes of t1 and t2 match.
          let eta = case _addressInfo'focus addressInfo of
                FocusEliminee -> Eta False
                FocusWrapped -> Eta True
                NoFocus -> Eta True
          let maybeCSs = classifMust2will $ Twice1 <$> maybeCS1 <*> maybeCS2
          case _addressInfo'boredom addressInfo of
            EntirelyBoring -> checkASTRel eta relS gammadelta (Twice1 s1 s2) (Twice1 extraS1 extraS2) maybeCSs
            WorthMentioning -> do
              virtualConstraint <- defConstraint
                (JudRel (analyzableToken @sys @s) eta relS gammadelta
                  (Twice1 s1 s2)
                  (Twice1 extraS1 extraS2)
                  (classifMust2will $ Twice1 <$> maybeCS1 <*> maybeCS2)
                )
                ("Relating:" ++ (join $ (" > " ++ ) <$> _addressInfo'address addressInfo))
              withParent virtualConstraint $
                checkASTRel eta relS gammadelta (Twice1 s1 s2) (Twice1 extraS1 extraS2) maybeCSs
            WorthScheduling -> addNewConstraint
              (JudRel (analyzableToken @sys @s) eta relS gammadelta
                (Twice1 s1 s2)
                (Twice1 extraS1 extraS2)
                (classifMust2will $ Twice1 <$> maybeCS1 <*> maybeCS2)
              )
              ("Relating:" ++ (join $ (" > " ++ ) <$> _addressInfo'address addressInfo))
          return AnalysisRel
  case attempt of
    Right AnalysisRel -> return ()
    Left anErr -> case (anErr, analyzableToken :: AnalyzableToken sys t, t1) of
         (AnErrorTermMeta, AnTokenTermNV, TermMeta neutrality meta (Compose depcies) alg) ->
           unreachable -- terms are neutral at this point
         (AnErrorTermMeta, _, _) -> unreachable
         (AnErrorTermWildcard, AnTokenTermNV, TermWildcard) -> unreachable
         (AnErrorTermWildcard, _, _) -> unreachable
         (AnErrorTermQName, AnTokenTermNV, TermQName qname ldivVal) ->
           unreachable -- terms are neutral at this point
         (AnErrorTermQName, _, _) -> unreachable
         (AnErrorTermAlreadyChecked, AnTokenTermNV, TermAlreadyChecked tChecked tyChecked) ->
           unreachable -- terms are neutral at this point
         (AnErrorTermAlreadyChecked, _, _) -> unreachable
         (AnErrorTermAlgorithm, AnTokenTermNV, TermAlgorithm alg tResult) -> 
           unreachable -- terms are neutral at this point
         (AnErrorTermAlgorithm, _, _) -> unreachable
         --(AnErrorTermSys sysErr, _, _) ->
         --  checkUnanalyzableSysASTRel sysErr eta relT gamma t1 t2 maybeCTs
         (AnErrorTermProblem, AnTokenTermNV, TermProblem tProblem) -> tcFail "False"
         (AnErrorTermProblem, _, _) -> unreachable
         (AnErrorVar, AnTokenTerm, Var2 v1) -> case t2 of
           (Var2 v2) -> if v1 == v2
             then return ()
             else tcFail "Cannot relate different variables."
           _ -> tcFail "False"
         (AnErrorVar, _, _) -> unreachable
         (AnErrorSys sysErr, _, _) ->
           checkUnanalyzableSysASTRel' sysErr eta relT gamma (Twice1 t1 t2) (Twice1 extraT1 extraT2) maybeCTs

checkASTRel :: forall sys tc t v .
  (SysTC sys, MonadTC sys tc, DeBruijnLevel v, Analyzable sys t) =>
  Eta ->
  Relation t v ->
  Ctx (Twice2 Type) sys v Void ->
  Twice1 t v ->
  Twice1 (ClassifExtraInput t) v ->
  ClassifInfo (Twice1 (Classif t) v) ->
  tc ()
checkASTRel eta relT gamma ts@(Twice1 t1 t2) extraTs@(Twice1 extraT1 extraT2) maybeCTs =
  if quickEq @sys t1 t2 extraT1 extraT2
  then return ()
  else case analyzableToken @sys @t of
    AnTokenTerm -> checkTermRel eta relT gamma ts maybeCTs
    AnTokenSys sysToken ->             checkMultimodeOrSysASTRel (Right sysToken)      eta relT gamma ts extraTs maybeCTs
    AnTokenMultimode multimodeToken -> checkMultimodeOrSysASTRel (Left multimodeToken) eta relT gamma ts extraTs maybeCTs
    _ -> checkASTRel' eta relT gamma ts extraTs maybeCTs

---------------------------------------------------

checkTermRelWHNTermsNoEta :: (SysTC sys, MonadTC sys tc, DeBruijnLevel v) =>
  ModedDegree sys v ->
  Ctx (Twice2 Type) sys v Void ->
  Term sys v ->
  Term sys v ->
  Type sys v ->
  Type sys v ->
  [Int] ->
  [Int] ->
  tc ()
checkTermRelWHNTermsNoEta deg gamma t1 t2 ty1 ty2 metasTy1 metasTy2 =
  checkASTRel' (Eta False) deg gamma (Twice1 t1 t2) (Twice1 U1 U1) (ClassifWillBe $ Twice1 ty1 ty2)

checkTermRelNoEta :: (SysTC sys, MonadTC sys tc, DeBruijnLevel v) =>
  ModedDegree sys v ->
  Ctx (Twice2 Type) sys v Void ->
  Term sys v ->
  Term sys v ->
  Term sys v ->
  Term sys v ->
  [Int] ->
  [Int] ->
  Type sys v ->
  Type sys v ->
  [Int] ->
  [Int] ->
  tc ()
checkTermRelNoEta deg gamma t1 t2 nonwhnt1 nonwhnt2 metasT1 metasT2 ty1 ty2 metasTy1 metasTy2 = do
  case (isBlockedOrMeta t1 metasT1, isBlockedOrMeta t2 metasT2) of
    -- Both are whnormal
    (False, False) -> checkTermRelWHNTermsNoEta deg gamma t1 t2 ty1 ty2 metasTy1 metasTy2
    -- Only one is whnormal: whsolve or block
    (True , False) -> tryToSolveTerm (Eta False) deg          gamma  t1 t2 nonwhnt2 ty1 ty2 metasTy1 metasTy2
      $ tcBlock
    (False, True ) -> tryToSolveTerm (Eta False) deg (flipCtx gamma) t2 t1 nonwhnt1 ty2 ty1 metasTy2 metasTy1
      $ tcBlock
    -- Neither is whnormal: block
    (True , True ) -> tcBlock "Cannot solve relation: both sides are blocked on a meta-variable."

--------------------------------------------------------
-- MAYBE ETA --
--------------------------------------------------------

-- | This should preferrably be implemented using TC.ASTSolve.etaExpand
etaExpandIfApplicable :: (SysTC sys, MonadTC sys tc, DeBruijnLevel v) =>
  ModedDegree sys v ->
  Ctx (Twice2 Type) sys v Void ->
  Term sys v ->
  Term sys v ->
  Term sys v ->
  Term sys v ->
  [Int] ->
  [Int] ->
  UniHSConstructor sys v ->
  UniHSConstructor sys v ->
  tc ()
etaExpandIfApplicable ddeg gamma t1 t2 nonwhnt1 nonwhnt2 metasT1 metasT2 ty1 ty2 = do
  let dgamma' = ctx'mode gamma
  let dgamma = unVarFromCtx <$> dgamma'
  --let giveUp = checkTermRelNoEta ddeg gamma t1 t2 nonwhnt1 nonwhnt2 metasT1 metasT2 (hs2type ty1) (hs2type ty2) [] []
  maybeMaybeExpandT1 <- etaExpand UseEliminees (fstCtx gamma) t1 ty1
  maybeMaybeExpandT2 <- etaExpand UseEliminees (sndCtx gamma) t2 ty2
  let maybeMaybeExpansions = getCompose $ (,) <$> Compose maybeMaybeExpandT1 <*> Compose maybeMaybeExpandT2
  case maybeMaybeExpansions of
    Just (Just (expandT1, expandT2)) ->
      addNewConstraint
        (JudTermRel
          (Eta False)
          ddeg
          gamma
          (Twice2 expandT1 expandT2)
          (Twice2 (hs2type ty1) (hs2type ty2))
        )
        "Eta-expand."
    Just Nothing -> return ()
    Nothing -> tcBlock $ "Need to know if types have eta."

checkTermRelMaybeEta :: (SysTC sys, MonadTC sys tc, DeBruijnLevel v) =>
  ModedDegree sys v ->
  Ctx (Twice2 Type) sys v Void ->
  Term sys v ->
  Term sys v ->
  Term sys v ->
  Term sys v ->
  [Int] ->
  [Int] ->
  UniHSConstructor sys v ->
  UniHSConstructor sys v ->
  tc ()
checkTermRelMaybeEta deg gamma t1 t2 nonwhnt1 nonwhnt2 metasT1 metasT2 ty1 ty2 = do
  let callEtaExpandIfApplicable = etaExpandIfApplicable deg gamma t1 t2 nonwhnt1 nonwhnt2 metasT1 metasT2 ty1 ty2
  case (isBlockedOrMeta t1 metasT1, isBlockedOrMeta t2 metasT2) of
    (False, False) -> callEtaExpandIfApplicable
    (True , False) ->
      tryToSolveTerm (Eta True) deg          gamma  t1 t2 nonwhnt2 (hs2type ty1) (hs2type ty2) [] []
      $ const callEtaExpandIfApplicable
    (False, True ) ->
      tryToSolveTerm (Eta True) deg (flipCtx gamma) t2 t1 nonwhnt1 (hs2type ty2) (hs2type ty1) [] []
      $ const callEtaExpandIfApplicable
    (True , True ) -> tcBlock "Cannot solve relation: both sides are blocked on a meta-variable."

---------------------------------------------------

checkTermRel :: forall sys tc v .
  (SysTC sys, MonadTC sys tc, DeBruijnLevel v) =>
  Eta ->
  ModedDegree sys v ->
  Ctx (Twice2 Type) sys v Void ->
  Twice1 (Term sys) v ->
  ClassifInfo (Twice1 (Type sys) v) ->
  tc ()
checkTermRel eta ddeg gamma (Twice1 nonwhnt1 nonwhnt2) maybeTys = do
  let Twice1 ty1 ty2 = fromClassifInfo unreachable maybeTys
  let dgamma' = ctx'mode gamma
  let dgamma = unVarFromCtx <$> dgamma'
  -- Top-relatedness is always ok.
  itIsTopDeg <- isTopDeg (crispModedModality dgamma' :\\ fstCtx gamma) (_degree'deg ddeg) dgamma
    "Need to know whether required ddegree of relatedness is Top."
  case itIsTopDeg of
    -- It's certainly about top-relatedness
    Just True -> return ()
    -- We don't know
    Nothing -> tcBlock $ "Need to know whether required ddegree of relatedness is Top."
    -- It's certainly not about top-relatedness
    Just False -> do
      -- purposefully shadowing (redefining)
      (ty1, metasTy1) <- runWriterT $ whnormalizeType (fstCtx gamma) ty1 "Weak-head-normalizing first type."
      (ty2, metasTy2) <- runWriterT $ whnormalizeType (sndCtx gamma) ty2 "Weak-head-normalizing second type."
      (t1, metasT1) <- runWriterT $ whnormalize (fstCtx gamma) nonwhnt1 ty1 "Weak-head-normalizing first term."
      (t2, metasT2) <- runWriterT $ whnormalize (sndCtx gamma) nonwhnt2 ty2 "Weak-head-normalizing second term."
      parent <- defConstraint
            (JudTermRel
              eta
              ddeg
              gamma
              (Twice2 t1 t2)
              (Twice2 ty1 ty2)
            )
            "Weak-head-normalize everything"

      withParent parent $ if unEta eta
        then case (unType ty1, unType ty2) of
               (Expr2 (TermCons (ConsUniHS tycode1)), Expr2 (TermCons (ConsUniHS tycode2))) ->
                 checkTermRelMaybeEta ddeg gamma t1 t2 nonwhnt1 nonwhnt2 metasT1 metasT2 tycode1 tycode2
               (_, _) -> case (isBlockedOrMeta (unType ty1) metasTy1, isBlockedOrMeta (unType ty2) metasTy2) of
                 (False, False) -> checkTermRelNoEta ddeg gamma t1 t2 nonwhnt1 nonwhnt2 metasT1 metasT2 ty1 ty2 [] []
                 (_    , _    ) ->
                   tcBlock $ "Need to weak-head-normalize types to tell whether I should use eta-expansion."
        else checkTermRelNoEta ddeg gamma t1 t2 nonwhnt1 nonwhnt2 metasT1 metasT2 ty1 ty2 [] []
