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
import Control.Monad.Trans.Writer.Lazy

{-
instance Monoid a => Monad (Const a) where
  return = pure
  Const a >>= f = let Const b = f unreachable
                  in  Const $ a <> b
-}

quickEq :: forall sys t v .
  (SysAnalyzer sys, Analyzable sys t, DeBruijnLevel v) =>
  t v ->
  t v ->
  ClassifExtraInput t v ->
  ClassifExtraInput t v ->
  Bool
quickEq t t' extraT extraT' =
  let result = fmap execWriter $ analyze @sys @t @_ @_ @v TokenRel unreachable
        (Classification t extraT ClassifUnknown)
        $ \ wkn _ extract extCtx extractRel addressInfo ->
          case (extract unreachable (Classification t  extraT  ClassifUnknown),
                extract unreachable (Classification t' extraT' ClassifUnknown)) of
            (Nothing, _) -> unreachable
            (Just _, Nothing) -> writer (AnalysisRel, All False)
            (Just (Classification s  extraS  _),
             Just (Classification s' extraS' _)) -> writer (AnalysisRel, All $ quickEq @sys s s' extraS extraS')
  in case result of
       Right (All b) -> b
       Left anErr -> case (anErr, analyzableToken @sys @t, t) of
         (AnErrorTermMeta, AnTokenTermNV, TermMeta neutrality meta (Compose depcies) alg) -> case t' of
           TermMeta neutrality' meta' (Compose depcies') alg' ->
             (neutrality == neutrality')
             && meta == meta'
             && length depcies == length depcies'
             && and (zip depcies depcies' <&> \ (depcy, depcy') -> quickEq @sys depcy depcy' U1 U1)
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
               U1 U1
           _ -> False
         (AnErrorTermQName, _, _) -> unreachable
         (AnErrorTermAlreadyChecked, AnTokenTermNV, TermAlreadyChecked tChecked tyChecked) -> case t' of
           (TermAlreadyChecked tChecked' tyChecked') -> quickEq @sys tChecked tChecked' U1 U1
           _ -> False
         (AnErrorTermAlreadyChecked, _, _) -> unreachable
         (AnErrorTermAlgorithm, AnTokenTermNV, TermAlgorithm alg tResult) -> case t' of
           (TermAlgorithm alg' tResult') -> quickEq @sys tResult tResult' U1 U1
           _ -> False
         (AnErrorTermAlgorithm, _, _) -> unreachable
         (AnErrorTermProblem, AnTokenTermNV, TermProblem tProblem) -> False
         (AnErrorTermProblem, _, _) -> unreachable
         (AnErrorVar, AnTokenTerm, Var2 v) -> case t' of
           (Var2 v') -> v == v'
           _ -> False
         (AnErrorVar, _, _) -> unreachable
         (AnErrorSys sysError, _, _) -> quickEqSysUnanalyzable sysError t t' extraT extraT'
