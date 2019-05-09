{-# LANGUAGE AllowAmbiguousTypes #-}

module Menkar.TC.QuickEq where

import Menkar.Fine
import Menkar.Analyzer
import Menkar.WHN

import Control.Exception.AssertFalse

import Data.Functor.Identity
import Data.Functor.Compose
import Data.Monoid
import Data.Functor.Const
import Control.Lens
import GHC.Generics

quickEq :: forall sys t v .
  (SysAnalyzer sys, Analyzable sys t, DeBruijnLevel v) =>
  t v -> t v -> AnalyzerExtraInput t v -> Bool
quickEq t t' extraT =
  let result = fmap getConst $ analyze @sys @t TokenRelate id unreachable
        (AnalyzerInput t extraT ClassifUnknown (IfRelate $ unreachable))
        $ \ wkn _ (AnalyzerInput s extraS _ _) addressInfo extract ->
          case extract t' of
            Nothing -> Const $ All False
            Just s' -> Const $ All $ quickEq @sys s s' extraS
  in case result of
       Right (All b) -> b
       Left anErr -> case (anErr, analyzableToken @sys @t, t) of
         (AnErrorTermMeta, AnTokenTermNV, TermMeta neutrality meta (Compose depcies) alg) -> case t' of
           TermMeta neutrality' meta' (Compose depcies') alg' ->
             (neutrality == neutrality')
             && meta == meta'
             && length depcies == length depcies'
             && and (zip depcies depcies' <&> \ (depcy, depcy') -> quickEq @sys depcy depcy' U1)
           _ -> False
         (AnErrorTermMeta, _, _) -> unreachable
         (AnErrorTermWildcard, AnTokenTermNV, TermWildcard) -> unreachable
         (AnErrorTermWildcard, _, _) -> unreachable
         (AnErrorTermQName, AnTokenTermNV, TermQName qname ldivVal) -> case t' of
           TermQName qname' ldivVal' ->
             qname == qname'
             && quickEq @sys
               (_leftDivided'content $ ldivVal)
               (_leftDivided'content $ ldivVal')
               U1
           _ -> False
         (AnErrorTermQName, _, _) -> unreachable
         (AnErrorTermAlreadyChecked, AnTokenTermNV, TermAlreadyChecked tChecked tyChecked) -> case t' of
           (TermAlreadyChecked tChecked' tyChecked') -> quickEq @sys tChecked tChecked' U1
           _ -> False
         (AnErrorTermAlreadyChecked, _, _) -> unreachable
         (AnErrorTermAlgorithm, AnTokenTermNV, TermAlgorithm alg tResult) -> case t' of
           (TermAlgorithm alg' tResult') -> quickEq @sys tResult tResult' U1
           _ -> False
         (AnErrorTermAlgorithm, _, _) -> unreachable
         (AnErrorTermSys, AnTokenTermNV, TermSys syst) -> _
         (AnErrorTermSys, _, _) -> unreachable
         (AnErrorTermProblem, AnTokenTermNV, TermProblem tProblem) -> False
         (AnErrorTermProblem, _, _) -> unreachable
         (AnErrorVar, AnTokenTerm, Var2 v) -> case t' of
           (Var2 v') -> v == v'
           _ -> False
