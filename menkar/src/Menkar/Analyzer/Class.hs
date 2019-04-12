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
  _maybeClassified'maybeClassifier :: Maybe (Classif t v),
  _maybeClassified'maybeRelation :: Maybe (Relation t v)}

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
  type Relation t :: * -> *
  analyze :: forall option f v .
    (Applicative f, DeBruijnLevel v) =>
    AnalyzerToken option ->
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
    Maybe (f (AnalyzerResult option t v))

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
  Maybe (f (t v))
subtermsTyped h gamma maybeClassifiedT = fmap unbox1 <$> analyze TokenSubterms
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
  Maybe (f (t v))
subterms h gamma t = subtermsTyped
  (\ wkn gamma maybeClassifiedS addressInfo -> h wkn gamma (_maybeClassified'get maybeClassifiedS) addressInfo)
  gamma (MaybeClassified t Nothing Nothing)

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
  Maybe (f (Classif t v))
typetrick h gamma maybeClassifiedT = fmap unboxClassif <$> analyze TokenTypes
  (\ wkn gamma maybeClassifiedS addressInfo -> BoxClassif <$> h wkn gamma maybeClassifiedS addressInfo)
  gamma maybeClassifiedT
