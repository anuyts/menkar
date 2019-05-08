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
            cs <- _newMetaClassif
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
    Left anErr -> case (anErr, analyzableToken :: AnalyzableToken sys t, t) of
      (AnErrorTermMeta, AnTokenTermNV, TermMeta neutrality meta depcies alg) -> _meta
      (AnErrorTermMeta, _, _) -> unreachable
      (AnErrorTermWildcard, AnTokenTermNV, TermWildcard) -> unreachable
      (AnErrorTermWildcard, _, _) -> unreachable
      (AnErrorTermQName, AnTokenTermNV, TermQName qname ldivVal) -> _qname
      (AnErrorTermQName, _, _) -> unreachable
      (AnErrorTermAlreadyChecked, AnTokenTermNV, TermAlreadyChecked tChecked ty) -> _alreadyChecked
      (AnErrorTermAlreadyChecked, _, _) -> unreachable
      (AnErrorTermAlgorithm, AnTokenTermNV, TermAlgorithm alg tResult) -> _algorithm
      (AnErrorTermAlgorithm, _, _) -> unreachable
      (AnErrorTermSys, AnTokenTermNV, TermSys syst) -> _sys
      (AnErrorTermSys, _, _) -> unreachable
      (AnErrorTermProblem, AnTokenTermNV, TermProblem tProblem) -> _problem
      (AnErrorTermProblem, _, _) -> unreachable
      (AnErrorVar, AnTokenTerm, Var2 v) -> _var
      (AnErrorVar, _, _) -> unreachable

checkAST :: forall sys tc v t .
  (SysTC sys, MonadTC sys tc, DeBruijnLevel v, Analyzable sys t, Analyzable sys (Classif t)) =>
  Constraint sys ->
  Ctx Type sys v Void ->
  t v ->
  ClassifInfo (Classif t v) ->
  tc ()
checkAST parent gamma t maybeCT = _
