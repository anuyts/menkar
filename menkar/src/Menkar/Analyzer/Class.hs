module Menkar.Analyzer.Class where

import Menkar.Basic.Context
import Menkar.Fine.Syntax
import Menkar.Fine.Context

import Data.Functor.Coerce

import Control.Lens
import Data.Kind hiding (Type)
import Data.Void

data AnalyzerOption = OptionSubterms | OptionTypes
data AnalyzerToken (option :: AnalyzerOption) where
  TokenSubterms :: AnalyzerToken OptionSubterms
  TokenTypes :: AnalyzerToken OptionTypes

newtype BoxClassif t v = BoxClassif {unboxClassif :: Classif t v}

data MaybeClassified t v = MaybeClassified {
  _maybeClassified'get :: t v,
  _maybeClassified'maybeClassifier :: Maybe (Classif t v)}

data AddressInfo = AddressInfo {
  {-| Deepest last -}
  _addressInfo'address :: [String],
  _addressInfo'shouldWHN :: Bool
  }

type family AnalyzerResult (option :: AnalyzerOption) = (result :: (* -> *) -> * -> *) | result -> option
type instance AnalyzerResult OptionSubterms = Box1
type instance AnalyzerResult OptionTypes = BoxClassif

class Analyzable sys t where
  type Classif t :: * -> *
  analyze :: forall option f v .
    (Applicative f, DeBruijnLevel v) =>
    (forall s w .
      (Analyzable sys s, DeBruijnLevel w) =>
      (v -> w) ->
      Ctx Type sys w Void ->
      MaybeClassified s w ->
      AddressInfo ->
      f (AnalyzerResult option s w)
    ) ->
    Ctx Type sys v Void ->
    MaybeClassified t v ->
    f (AnalyzerResult option t v)

subtermsTyped :: forall sys f t v .
  (Applicative f, Analyzable sys t, DeBruijnLevel v) =>
  (forall s w .
    (Analyzable sys s, DeBruijnLevel w) =>
    (v -> w) ->
    Ctx Type sys w Void ->
    MaybeClassified s w ->
    AddressInfo ->
    f (s w)
  ) ->
  Ctx Type sys v Void ->
  MaybeClassified t v ->
  f (t v)
subtermsTyped h gamma maybeClassifiedT = unbox1 <$> analyze
  (\ wkn gamma maybeClassifiedS addressInfo -> Box1 <$> h wkn gamma maybeClassifiedS addressInfo)
  gamma maybeClassifiedT

subterms :: forall sys f t v .
  (Applicative f, Analyzable sys t, DeBruijnLevel v) =>
  (forall s w .
    (Analyzable sys s, DeBruijnLevel w) =>
    (v -> w) ->
    Ctx Type sys w Void ->
    s w ->
    AddressInfo ->
    f (s w)
  ) ->
  Ctx Type sys v Void ->
  t v ->
  f (t v)
subterms h gamma t = subtermsTyped
  (\ wkn gamma maybeClassifiedS addressInfo -> h wkn gamma (_maybeClassified'get maybeClassifiedS) addressInfo)
  gamma (MaybeClassified t Nothing)

typetrick :: forall sys f t v .
  (Applicative f, Analyzable sys t, DeBruijnLevel v) =>
  (forall s w .
    (Analyzable sys s, DeBruijnLevel w) =>
    (v -> w) ->
    Ctx Type sys w Void ->
    MaybeClassified s w ->
    AddressInfo ->
    f (Classif s w)
  ) ->
  Ctx Type sys v Void ->
  MaybeClassified t v ->
  f (Classif t v)
typetrick h gamma maybeClassifiedT = unboxClassif <$> analyze
  (\ wkn gamma maybeClassifiedS addressInfo -> BoxClassif <$> h wkn gamma maybeClassifiedS addressInfo)
  gamma maybeClassifiedT
