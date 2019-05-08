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

import Data.Void
import Control.Lens
import Data.Functor.Compose
import Control.Monad
import Control.Monad.Writer.Lazy
import GHC.Generics

----------------------------

{-| Same as quickInfer, but with the precondition that the given AST admits analysis.
-}
quickInferUnsafe :: forall sys tc v t .
  (SysTC sys, MonadTC sys tc, DeBruijnLevel v, Analyzable sys t, Analyzable sys (Classif t)) =>
  Constraint sys ->
  Ctx Type sys v Void ->
  t v ->
  AnalyzerExtraInput t v ->
  [String] -> 
  tc (Classif t v)
quickInferUnsafe parent gamma t extraT address = do
    maybeCT <- sequenceA $ typetrick id gamma (AnalyzerInput t extraT ClassifUnknown IfRelateTypes) $
      \ wkn gammadelta (AnalyzerInput s extraS maybeCS _) addressInfo ->
        quickInfer parent gammadelta s extraS (address ++ _addressInfo'address addressInfo)
    case maybeCT of
      Right ct -> return ct
      Left _ -> unreachable

{-| Quickly generates a classifier for a given AST. If the AST is classifiable, then it will
    classifier-check under the returned classifier, which however can contain metas.
-}
quickInfer :: forall sys tc v t .
  (SysTC sys, MonadTC sys tc, DeBruijnLevel v, Analyzable sys t, Analyzable sys (Classif t)) =>
  Constraint sys ->
  Ctx Type sys v Void ->
  t v ->
  AnalyzerExtraInput t v ->
  [String] -> 
  tc (Classif t v)
quickInfer parent gamma t extraT address = case (analyzableToken :: AnalyzableToken sys t) of
  AnTokenTerm -> newMetaType (Just parent) gamma $ join $ (" > " ++) <$> address
  AnTokenTermNV -> newMetaType (Just parent) gamma $ join $ (" > " ++) <$> address
  -- TODO: dispatch system-specific tokens
  _ -> quickInferUnsafe parent gamma t extraT address

----------------------------

checkSpecialAST :: forall sys tc v t .
  (SysTC sys, MonadTC sys tc, DeBruijnLevel v, Analyzable sys t, Analyzable sys (Classif t)) =>
  Constraint sys ->
  Ctx Type sys v Void ->
  AnalyzerError sys ->
  t v ->
  AnalyzerExtraInput t v ->
  ClassifInfo (Classif t v) ->
  tc (Classif t v)
checkSpecialAST parent gamma anErr t extraT maybeCT = do
  case (anErr, analyzableToken :: AnalyzableToken sys t, t) of
    (AnErrorTermMeta, AnTokenTermNV, TermMeta neutrality meta (Compose depcies) alg) -> do
      maybeT <- awaitMeta parent "I want to know what I'm supposed to type-check." meta depcies
      t' <- case maybeT of
        Nothing -> do
          -- Ideally, terms are type-checked only once. Hence, the first encounter is the best
          -- place to request eta-expansion.
          case neutrality of
            MetaBlocked -> addNewConstraint
              (JudEta gamma (Expr2 t) (fromClassifInfo unreachable maybeCT))
              (Just parent)
              "Eta-expand meta if possible."
            MetaNeutral -> return ()
          tcBlock parent "I want to know what I'm supposed to type-check."
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
        (Jud analyzableToken gamma t' maybeCT)
        (Just parent)
        "Look up meta."
      checkAST' childConstraint gamma t' U1 maybeCT
    (AnErrorTermMeta, _, _) -> unreachable
    (AnErrorTermWildcard, AnTokenTermNV, TermWildcard) -> unreachable
    (AnErrorTermWildcard, _, _) -> unreachable
    (AnErrorTermQName, AnTokenTermNV, TermQName qname ldivVal) -> do
      let (LeftDivided d2 d1mu telescope) = ldivVal
      let ldivModAppliedValRHS = (leftDivided'content .~ telescoped2modalQuantified d2 telescope) ldivVal
      addNewConstraint
        (JudRel AnTokenModedModality (Const ModLeq)
          (duplicateCtx gamma)
          (Twice1
            (_modApplied'modality . _leftDivided'content $ ldivModAppliedValRHS)
            (_leftDivided'modality $ ldivModAppliedValRHS)
          )
          ClassifUnknown
        )
        (Just parent)
        "Checking that variable is accessible."
      return $ _val'type . _modApplied'content . _leftDivided'content $ ldivModAppliedValRHS
    (AnErrorTermQName, _, _) -> unreachable
    --(AnErrorTermAlreadyChecked, AnTokenTermNV, TermAlreadyChecked tChecked ty) -> _alreadyChecked
    (AnErrorTermAlreadyChecked, _, _) -> unreachable
    --(AnErrorTermAlgorithm, AnTokenTermNV, TermAlgorithm alg tResult) -> _algorithm
    (AnErrorTermAlgorithm, _, _) -> unreachable
    --(AnErrorTermSys, AnTokenTermNV, TermSys syst) -> _sys
    (AnErrorTermSys, _, _) -> unreachable
    --(AnErrorTermProblem, AnTokenTermNV, TermProblem tProblem) -> _problem
    (AnErrorTermProblem, _, _) -> unreachable
    --(AnErrorVar, AnTokenTerm, Var2 v) -> _var
    (AnErrorVar, _, _) -> unreachable
    _ -> _ 

{-| Equality of expected and actual classifier is checked on the outside IF requested. -}
checkAST' :: forall sys tc v t .
  (SysTC sys, MonadTC sys tc, DeBruijnLevel v, Analyzable sys t, Analyzable sys (Classif t)) =>
  Constraint sys ->
  Ctx Type sys v Void ->
  t v ->
  AnalyzerExtraInput t v ->
  ClassifInfo (Classif t v) ->
  tc (Classif t v)
checkAST' parent gamma t extraT maybeCT = do
  maybeCTInferred <- sequenceA $ typetrick id gamma (AnalyzerInput t extraT maybeCT IfRelateTypes) $
    \ wkn gammadelta (AnalyzerInput s extraS maybeCS _) addressInfo -> case _addressInfo'boredom addressInfo of
      -- entirely boring: pass on and return inferred and certified type. 
      EntirelyBoring -> checkAST' parent gammadelta s extraS maybeCS
      -- worth mentioning: pass on and return inferred and certified type.
      WorthMentioning -> do
        virtualConstraint <- defConstraint
          (Jud analyzableToken gammadelta s maybeCS)
          (Just parent)
          ("Typecheck: " ++ (join $ _addressInfo'address addressInfo))
        checkAST' virtualConstraint gammadelta s extraS maybeCS
      -- worth scheduling: schedule.
      WorthScheduling -> do
        (cs, maybeCS) <- case maybeCS of
          -- if a certified type is given, write it in judgement (it is still certified) and pass it back.
          ClassifWillBe cs -> return $ (cs, ClassifWillBe cs)
          -- if an expected type is given, write it in judgement (thus certifying it) and pass it back.
          ClassifMustBe cs -> return $ (cs, ClassifMustBe cs)
          -- if no type is given, write a meta in judgement (thus certifying it) and pass it back.
          ClassifUnknown -> do
            cs <- quickInfer parent gammadelta s extraS $ _addressInfo'address addressInfo
            return $ (cs, ClassifMustBe cs)
        addNewConstraint
          (Jud analyzableToken gammadelta s maybeCS)
          (Just parent)
          ("Typecheck: " ++ (join $ _addressInfo'address addressInfo))
        return cs
  case maybeCTInferred of
    Right ctInferred -> do
      case maybeCT of
        ClassifMustBe ct -> addNewConstraint
          (JudRel analyzableToken
            (convRel (analyzableToken :: AnalyzableToken sys t) $ unVarFromCtx <$> ctx'mode gamma)
            (duplicateCtx gamma)
            (Twice1 ctInferred ct)
            ClassifUnknown)
          (Just parent)
          ("Checking whether actual classifier equals expected classifier.")
        _ -> return ()
      return ctInferred
    Left anErr -> checkSpecialAST parent gamma anErr t extraT maybeCT

{-
checkAST :: forall sys tc v t .
  (SysTC sys, MonadTC sys tc, DeBruijnLevel v, Analyzable sys t, Analyzable sys (Classif t)) =>
  Constraint sys ->
  Ctx Type sys v Void ->
  t v ->
  ClassifInfo (Classif t v) ->
  tc ()
checkAST parent gamma t maybeCT = _
-}
