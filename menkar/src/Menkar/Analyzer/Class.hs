module Menkar.Analyzer.Class where

import Menkar.Basic.Context
import Menkar.Fine.Syntax
import Menkar.Fine.Context

import Data.Functor.Coerce

import Control.Lens
import Data.Kind hiding (Type)
import Data.Void
import Data.Functor.Identity
import GHC.Generics

data AnalyzerOption = OptionSubterms | OptionTypes | OptionRelate
data AnalyzerToken (option :: AnalyzerOption) where
  TokenSubterms :: AnalyzerToken OptionSubterms
  TokenTypes :: AnalyzerToken OptionTypes
  TokenRelate :: AnalyzerToken OptionRelate

newtype BoxClassif t v = BoxClassif {unboxClassif :: Classif t v}

data MaybeClassified (option :: AnalyzerOption) (t :: * -> *) (v :: *) = MaybeClassified {
  _maybeClassified'get :: t v,
  _maybeClassified'maybeClassifier :: Maybe (Classif t v),
  _maybeClassified'relation :: IfRelate option (Relation t v)}

data AddressInfo = AddressInfo {
  {-| Deepest last -}
  _addressInfo'address :: [String],
  _addressInfo'shouldWHN :: Bool
  }

type family AnalyzerResult (option :: AnalyzerOption) = (result :: (* -> *) -> * -> *) | result -> option
type instance AnalyzerResult OptionSubterms = Box1
type instance AnalyzerResult OptionTypes = BoxClassif
type instance AnalyzerResult OptionRelate = Unit2

data IfRelate (option :: AnalyzerOption) a where
  IfRelateSubterms :: IfRelate OptionSubterms a
  IfRelateTypes :: IfRelate OptionTypes a
  IfRelate :: a -> IfRelate OptionRelate a

deriving instance Functor (IfRelate option)

toIfRelate :: AnalyzerToken option -> a -> IfRelate option a
toIfRelate TokenSubterms a = IfRelateSubterms
toIfRelate TokenTypes a = IfRelateTypes
toIfRelate TokenRelate a = IfRelate a

{-| A supercombinator for type-checking, relatedness-checking, weak-head-normalization, normalization,
    weak-head-meta-resolution and more.

    Idea:
    - From above, you get
      - a context,
      - an AST,
      - maybe an expected classifier (which you probably don't need FOR TERMS),
      - maybe a relation.
    - For each subAST you pass back
      - an adapted context (+ weakening operation),
      - the subAST
      - maybe an expected classifier
      - a relation iff you got one from above
      - a title for the subAST
      - whether this subAST should be whnormal for the entire AST to be whnormal.

    In option "subterms", a modified subAST is returned, which you should recollect to a bigger AST of the same shape.

    In option "types", the type-checker checks the subASTs, makes sure their inferred type matches the expected type
    if you provided one, and passes you back the expected/inferred classifier. You should collect these into a classifier
    of the entire AST.

    In option "relate", nothing is returned, so there's nothing you need to do!

    Some principles:
    - You probably don't want to use the input classifier given through the last argument.
    - Since you cannot allocate metas, you should pass down either a complete classifier or no classifier.
      Hence, if you know something about a subAST's classifier, please know all about it.
-}
class (Functor t) => Analyzable sys t where
  type Classif t :: * -> *
  type Relation t :: * -> *
  analyze :: forall option lhs f v .
    (Applicative f, DeBruijnLevel v, Traversable (lhs sys)) =>
    AnalyzerToken option ->
    (forall w . Type sys w -> lhs sys w) ->
    (forall s w .
      (Analyzable sys s, DeBruijnLevel w) =>
      (v -> w) ->
      Ctx lhs sys w Void ->
      MaybeClassified option s w ->
      AddressInfo ->
      f (AnalyzerResult option s w)
    ) ->
    Ctx lhs sys v Void ->
    MaybeClassified option t v ->
    Maybe (f (AnalyzerResult option t v))

subtermsTyped :: forall sys f t v .
  (Applicative f, Analyzable sys t, DeBruijnLevel v, SysTrav sys) =>
  (forall s w .
    (Analyzable sys s, DeBruijnLevel w) =>
    (v -> w) ->
    Ctx Type sys w Void ->
    MaybeClassified OptionSubterms s w ->
    AddressInfo ->
    f (s w)
  ) ->
  Ctx Type sys v Void ->
  MaybeClassified OptionSubterms t v ->
  Maybe (f (t v))
subtermsTyped h gamma maybeClassifiedT = fmap unbox1 <$> analyze TokenSubterms id
  (\ wkn gamma maybeClassifiedS addressInfo -> Box1 <$> h wkn gamma maybeClassifiedS addressInfo)
  gamma maybeClassifiedT

subterms :: forall sys f t v .
  (Applicative f, Analyzable sys t, DeBruijnLevel v, SysTrav sys) =>
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
  gamma (MaybeClassified t Nothing IfRelateSubterms)

typetrick :: forall sys lhs f t v .
  (Applicative f, Analyzable sys t, DeBruijnLevel v, Traversable (lhs sys)) =>
  (forall w . Type sys w -> lhs sys w) ->
  (forall s w .
    (Analyzable sys s, DeBruijnLevel w) =>
    (v -> w) ->
    Ctx lhs sys w Void ->
    MaybeClassified OptionTypes s w ->
    AddressInfo ->
    f (Classif s w)
  ) ->
  Ctx lhs sys v Void ->
  MaybeClassified OptionTypes t v ->
  Maybe (f (Classif t v))
typetrick fromType h gamma maybeClassifiedT = fmap unboxClassif <$> analyze TokenTypes fromType
  (\ wkn gamma maybeClassifiedS addressInfo -> BoxClassif <$> h wkn gamma maybeClassifiedS addressInfo)
  gamma maybeClassifiedT
