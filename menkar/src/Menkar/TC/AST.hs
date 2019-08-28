module Menkar.TC.AST where

import Menkar.System
import Menkar.Fine.Syntax
import Menkar.Basic.Context
import Menkar.Fine.Context
import Menkar.Fine.Judgement
import Menkar.Fine.LookupQName
import qualified Menkar.Raw.Syntax as Raw
import Menkar.Monad.Monad
import Control.Exception.AssertFalse
import Menkar.Analyzer
import Menkar.WHN
--import Menkar.TC.Term
--import Menkar.TC.SmartElim
--import Menkar.TC.Rel
--import Menkar.TC.Entry
--import Menkar.TC.Segment
--import Menkar.TC.Solve

import Data.Functor.Functor1
import Data.Functor.Coyoneda.NF

import Data.Void
import Control.Lens
import Data.Functor.Compose
import Control.Monad
import Control.Monad.Writer.Strict
import GHC.Generics

----------------------------

{-
{-| Same as quickInfer, but with the precondition that the given AST admits analysis.
-}
quickInferNoCheckUnsafe :: forall sys tc v t .
  (SysTC sys, MonadTC sys tc, DeBruijnLevel v, Analyzable sys t, Analyzable sys (Classif t)) =>
  Constraint sys ->
  Ctx Type sys v ->
  t v ->
  ClassifExtraInput t v ->
  [String] -> 
  tc (Classif t v)
quickInferNoCheckUnsafe parent gamma t extraT address = do
    maybeCT <- sequenceA $ typetrick id gamma (Classification t extraT ClassifUnknown IfRelateTypes) $
      \ wkn gammadelta (Classification s extraS maybeCS _) addressInfo ->
        quickInferNoCheck parent gammadelta s extraS (address ++ _addressInfo'address addressInfo)
    case maybeCT of
      Right ct -> return ct
      Left _ -> unreachable

{-| Quickly generates a classifier for a given AST. If the AST is classifiable, then it will
    classifier-check under the returned classifier, which however can contain metas.
-}
quickInferNoCheck :: forall sys tc v t .
  (SysTC sys, MonadTC sys tc, DeBruijnLevel v, Analyzable sys t, Analyzable sys (Classif t)) =>
  Constraint sys ->
  Ctx Type sys v ->
  t v ->
  ClassifExtraInput t v ->
  [String] -> 
  tc (Classif t v)
quickInferNoCheck parent gamma t extraT address = case (analyzableToken :: AnalyzableToken sys t) of
  AnTokenTerm -> fmap Type $ newMetaTermNoCheck (Just parent) gamma MetaBlocked Nothing $ join $ (" > " ++) <$> address
  AnTokenTermNV -> fmap Type $ newMetaTermNoCheck (Just parent) gamma MetaBlocked Nothing $ join $ (" > " ++) <$> address
  -- TODO: dispatch system-specific tokens
  _ -> quickInferNoCheckUnsafe parent gamma t extraT address

quickInfer :: forall sys tc v t .
  (SysTC sys, MonadTC sys tc, DeBruijnLevel v, Analyzable sys t, Analyzable sys (Classif t)) =>
  Constraint sys ->
  Ctx Type sys v ->
  t v ->
  ClassifExtraInput t v ->
  [String] -> 
  tc (Classif t v)
quickInfer parent gamma t extraT address = do
  ct <- quickInferNoCheck parent gamma t extraT address
-}

----------------------------

checkSpecialAST :: forall sys tc v t .
  (SysTC sys, MonadTC sys tc, DeBruijnLevel v, Analyzable sys t, Analyzable sys (Classif t)) =>
  Ctx Type sys v ->
  AnalyzerError sys ->
  t v ->
  ClassifExtraInput t v ->
  ClassifInfo (Classif t v) ->
  tc (Classif t v)
checkSpecialAST gamma anErr t extraT maybeCT = do
  let ty = fromClassifInfo unreachable maybeCT
  let dgamma' = ctx'mode gamma
  let dgamma = dgamma'
  case (anErr, analyzableToken @sys @t, t) of
    (AnErrorTermMeta, AnTokenTermNV, TermMeta neutrality meta depcies alg) -> do
      maybeT <- awaitMeta @sys @tc @(Term sys) "I want to know what I'm supposed to type-check." meta depcies
      t' <- case maybeT of
        Nothing -> do
          -- Ideally, terms are type-checked only once. Hence, the first encounter is the best
          -- place to request eta-expansion.
          case neutrality of
            MetaBlocked -> addNewConstraint
              (JudEta analyzableToken gamma (Expr2 t) U1 ty)
              "Eta-expand meta if possible."
            MetaNeutral -> return ()
          tcBlock "I want to know what I'm supposed to type-check."
          {-
          -- The meta may now have a solution.
          maybeT' <- awaitMeta parent
                   "I want to know what I'm supposed to type-check. (Retry after trying to eta-expand)" meta depcies
          case maybeT' of
            Nothing -> tcBlock parent "I want to know what I'm supposed to type-check."
            Just t' -> return t'
          -}
        Just t' -> return t'
      childConstraint <- defConstraint
        (Jud analyzableToken gamma t' extraT (classifMust2will maybeCT))
        "Look up meta."
      withParent childConstraint $ checkAST gamma t' U1 (classifMust2will maybeCT)
    (AnErrorTermMeta, _, _) -> unreachable
    (AnErrorTermWildcard, AnTokenTermNV, TermWildcard) -> unreachable
    (AnErrorTermWildcard, _, _) -> unreachable
    (AnErrorTermQName, AnTokenTermNV, TermQName qname fsLDivVal) -> do
      let ldivVal = lowerFS $ fsLDivVal
      let (LeftDivided d2 d1mu telescope) = ldivVal
      let ldivModAppliedValRHS = (leftDivided'content .~ telescoped2modalQuantified d2 telescope) ldivVal
      let commonCod = _leftDivided'originalMode $ ldivVal
      addNewConstraint
        (JudRel analyzableToken (Eta True) (coy $ Const ModLeq)
          (duplicateCtx gamma)
          (Twice1
            (withDom $ _modApplied'modality . _leftDivided'content $ ldivModAppliedValRHS)
            (withDom $ _leftDivided'modality $ ldivModAppliedValRHS)
          )
          (Twice1 U1 U1)
          (ClassifWillBe $ Twice1 commonCod commonCod)
        )
        "Checking that definition is accessible."
      return $ _val'type . _modApplied'content . _leftDivided'content $ ldivModAppliedValRHS
    (AnErrorTermQName, _, _) -> unreachable
    (AnErrorTermAlreadyChecked, AnTokenTermNV, TermAlreadyChecked tChecked tyChecked) -> return tyChecked
    (AnErrorTermAlreadyChecked, _, _) -> unreachable
    (AnErrorTermAlgorithm, AnTokenTermNV, TermAlgorithm alg tResult) -> do
      --tyResult <- newMetaType (Just parent) gamma "Infer type of result."
      addNewConstraint
        (Jud AnTokenTerm gamma tResult U1 (ClassifWillBe ty))
        "Type-check the result."
      case alg of
        AlgSmartElim eliminee (Compose eliminators) -> do
          let dgamma = ctx'mode gamma
          let dmuElim = concatModedModalityDiagrammatically (fst1 <$> eliminators) $ uncoy dgamma
          tyEliminee <- newMetaType {-(eqDeg :: Degree sys _)-}
                        (withDom dmuElim :\\ gamma) "Infer type of eliminee."
          -----
          addNewConstraint
            (JudTerm (withDom dmuElim :\\ gamma) eliminee tyEliminee)
            "Type-check the eliminee."
          -----
          -----
          addNewConstraint
            (JudSmartElim gamma {-dmuElim-} eliminee tyEliminee eliminators tResult ty)
            "Smart elimination should reduce to its result."
        AlgGoal goalname depcies -> do
          goalConstraint <- defConstraint
            (JudGoal gamma goalname tResult ty)
            "Goal should take some value."
          withParent goalConstraint $ tcReport "This isn't my job; delegating to a human."
          -----
      return ty
    (AnErrorTermAlgorithm, _, _) -> unreachable
    --(AnErrorTermSys sysError, AnTokenTermNV, TermSys syst) -> inferTermSys sysError parent gamma syst
    --(AnErrorTermSys sysError, _, _) -> unreachable
    (AnErrorTermProblem, AnTokenTermNV, TermProblem tProblem) -> tcFail $ "Erroneous term."
    (AnErrorTermProblem, _, _) -> unreachable
    (AnErrorVar, AnTokenTerm, Var2 v) -> do
      let ldivSeg = uncoy $ lookupVar gamma v
      let commonCod = _leftDivided'originalMode $ ldivSeg
      addNewConstraint
        (JudRel AnTokenModalityTo (Eta True) (coy $ Const ModLeq)
          (crispCtx $ duplicateCtx gamma)
          (Twice1
            (_decl'modty . _leftDivided'content $ ldivSeg)
            (withDom $ _leftDivided'modality $ ldivSeg)
          )
          (Twice1 U1 U1)
          (ClassifWillBe $ Twice1 commonCod commonCod)
        )
        "Checking that variable is accessible."
      return $ _decl'content . _leftDivided'content $ ldivSeg
    (AnErrorVar, _, _) -> unreachable
    (AnErrorSys sysError, _, _) -> checkSysASTUnanalyzable sysError gamma t extraT maybeCT
    -- _ -> _ 

{-| Equality of expected and actual classifier is checked on the outside IF requested. -}
checkAST :: forall sys tc v t .
  (SysTC sys, MonadTC sys tc, DeBruijnLevel v, Analyzable sys t, Analyzable sys (Classif t)) =>
  Ctx Type sys v ->
  t v ->
  ClassifExtraInput t v ->
  ClassifInfo (Classif t v) ->
  tc (Classif t v)
checkAST gamma t extraT maybeCT = do
  let dgamma' = ctx'mode gamma
  let dgamma = dgamma'
  maybeCTInferred <- sequenceA $ typetrick gamma (Classification t extraT maybeCT) $
    \ wkn gammadelta (Classification (s :: s w) extraS maybeCS) addressInfo ->
      haveClassif @sys @s $
      case _addressInfo'boredom addressInfo of
        -- entirely boring: pass on and return inferred and certified type. 
        EntirelyBoring -> checkAST gammadelta s extraS maybeCS
        -- worth mentioning: pass on and return inferred and certified type.
        WorthMentioning -> do
          virtualConstraint <- defConstraint
            (Jud analyzableToken gammadelta s extraS maybeCS)
            ("Typecheck: " ++ (join $ _addressInfo'address addressInfo))
          withParent virtualConstraint $ checkAST gammadelta s extraS maybeCS
        -- worth scheduling: schedule.
        WorthScheduling -> do
          (cs, maybeCS) <- case maybeCS of
            -- if a certified type is given, write it in judgement (it is still certified) and pass it back.
            ClassifWillBe cs -> return $ (cs, ClassifWillBe cs)
            -- if an expected type is given, write it in judgement (thus certifying it) and pass it back.
            ClassifMustBe cs -> return $ (cs, ClassifMustBe cs)
            -- if no type is given, write a meta in judgement (thus certifying it) and pass it back.
            ClassifUnknown -> do
              cs <- newMetaClassif4ast gammadelta s extraS $
                "Inferring classifier: " ++ (join $ _addressInfo'address addressInfo)
              return $ (cs, ClassifMustBe cs)
          addNewConstraint
            (Jud analyzableToken gammadelta s extraS maybeCS)
            ("Typecheck: " ++ (join $ _addressInfo'address addressInfo))
          return cs
  ctInferred <- case maybeCTInferred of
    Right ctInferred -> return ctInferred
    Left anErr -> checkSpecialAST gamma anErr t extraT maybeCT
  case maybeCT of
        ClassifMustBe ct -> addNewConstraint
          (JudRel analyzableToken (Eta True)
            (coy $ convRel (analyzableToken :: AnalyzableToken sys t) $ dgamma)
            (duplicateCtx gamma)
            (Twice1 ctInferred ct)
            (Twice1 (extraClassif @sys dgamma t extraT) (extraClassif @sys dgamma t extraT))
            ClassifUnknown
          )
          ("Checking whether actual classifier equals expected classifier.")
        _ -> return ()
  return ctInferred
