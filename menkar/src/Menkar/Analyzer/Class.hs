module Menkar.Analyzer.Class where

import Menkar.Basic.Context
import Menkar.Fine.Syntax
import Menkar.Fine.Context

import Data.Functor.Coerce
import Data.Omissible

import Control.Lens
import Data.Kind hiding (Type)
import Data.Void
import Data.Functor.Identity
import GHC.Generics

data AnalyzerOption = OptionSubASTs | OptionTypes | OptionRelate
data AnalyzerToken (option :: AnalyzerOption) where
  TokenSubASTs :: AnalyzerToken OptionSubASTs
  TokenTypes :: AnalyzerToken OptionTypes
  TokenRelate :: AnalyzerToken OptionRelate

newtype BoxClassif t v = BoxClassif {unboxClassif :: Classif t v}

data ClassifInfo a = ClassifMustBe a | ClassifWillBe a | ClassifUnknown
  deriving (Functor, Foldable, Traversable)

classifMust2will :: ClassifInfo a -> ClassifInfo a
classifMust2will (ClassifMustBe a) = ClassifWillBe a
classifMust2will ca = ca

data AnalyzerInput (option :: AnalyzerOption) (t :: * -> *) (v :: *) = AnalyzerInput {
  _analyzerInput'get :: t v,
  _analyzerInput'extra :: AnalyzerExtraInput t v,
  _analyzerInput'classifInfo :: ClassifInfo (Classif t v),
  _analyzerInput'relation :: IfRelate option (Relation t v)}

data Boredom = EntirelyBoring | WorthMentioning | WorthScheduling

instance Omissible Boredom where
  omit = WorthScheduling

data AddressInfo = AddressInfo {
  {-| Deepest last -}
  _addressInfo'address :: [String],
  _addressInfo'shouldWHN :: Bool,
  _addressInfo'boredom :: Boredom
  }

type family AnalyzerResult (option :: AnalyzerOption) = (result :: (* -> *) -> * -> *) | result -> option
type instance AnalyzerResult OptionSubASTs = Box1
type instance AnalyzerResult OptionTypes = BoxClassif
type instance AnalyzerResult OptionRelate = Unit2

data IfRelate (option :: AnalyzerOption) a where
  IfRelateSubASTs :: IfRelate OptionSubASTs a
  IfRelateTypes :: IfRelate OptionTypes a
  IfRelate :: a -> IfRelate OptionRelate a

deriving instance Functor (IfRelate option)

toIfRelate :: AnalyzerToken option -> a -> IfRelate option a
toIfRelate TokenSubASTs a = IfRelateSubASTs
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

    In option "subASTs", a modified subAST is returned, which you should recollect to a bigger AST of the same shape.

    In option "types", the type-checker checks the subASTs, makes sure their inferred type matches the expected type
    if you provided one marked as 'ClassifMustBe',
    and passes you back the expected/inferred classifier. You should collect these into a classifier
    of the entire AST. The type-checker then checks that this classifier equals the expected one provided to you earlier.

    In option "relate", nothing is returned, so there's nothing you need to do!

    Some principles:
    - You probably don't want to use the input classifier given through the last argument.
    - Since you cannot allocate metas, you should pass down either a complete classifier or no classifier.
      Hence, if you know something about a subAST's classifier, please know all about it.
-}
class (Functor t, Functor (Relation t)) => Analyzable sys t where
  type AnalyzerExtraInput t :: * -> *
  type Classif t :: * -> *
  type Relation t :: * -> *
  analyze :: forall option lhs f v .
    (Applicative f, DeBruijnLevel v, Traversable (lhs sys)) =>
    AnalyzerToken option ->
    {-| For adding stuff to the context. -}
    (forall w . Type sys w -> lhs sys w) ->
    (forall s w .
      (Analyzable sys s, DeBruijnLevel w) =>
      (v -> w) ->
      Ctx lhs sys w Void ->
      AnalyzerInput option s w ->
      AddressInfo ->
      f (AnalyzerResult option s w)
    ) ->
    Ctx lhs sys v Void ->
    AnalyzerInput option t v ->
    Maybe (f (AnalyzerResult option t v))

subASTsTyped :: forall sys f t v .
  (Applicative f, Analyzable sys t, DeBruijnLevel v, SysTrav sys) =>
  (forall s w .
    (Analyzable sys s, DeBruijnLevel w) =>
    (v -> w) ->
    Ctx Type sys w Void ->
    AnalyzerInput OptionSubASTs s w ->
    AddressInfo ->
    f (s w)
  ) ->
  Ctx Type sys v Void ->
  AnalyzerInput OptionSubASTs t v ->
  Maybe (f (t v))
subASTsTyped h gamma inputT = fmap unbox1 <$> analyze TokenSubASTs id
  (\ wkn gamma inputS addressInfo -> Box1 <$> h wkn gamma inputS addressInfo)
  gamma inputT

subASTs :: forall sys f t v .
  (Applicative f, Analyzable sys t, DeBruijnLevel v, SysTrav sys) =>
  (forall s w .
    (Analyzable sys s, DeBruijnLevel w) =>
    (v -> w) ->
    Ctx Type sys w Void ->
    s w ->
    AnalyzerExtraInput s w ->
    AddressInfo ->
    f (s w)
  ) ->
  Ctx Type sys v Void ->
  t v ->
  AnalyzerExtraInput t v ->
  Maybe (f (t v))
subASTs h gamma t extraInputT = subASTsTyped
  (\ wkn gamma inputS addressInfo ->
     h wkn gamma (_analyzerInput'get inputS) (_analyzerInput'extra inputS) addressInfo
  )
  gamma (AnalyzerInput t extraInputT ClassifUnknown IfRelateSubASTs)

typetrick :: forall sys lhs f t v .
  (Applicative f, Analyzable sys t, DeBruijnLevel v, Traversable (lhs sys)) =>
  (forall w . Type sys w -> lhs sys w) ->
  (forall s w .
    (Analyzable sys s, DeBruijnLevel w) =>
    (v -> w) ->
    Ctx lhs sys w Void ->
    AnalyzerInput OptionTypes s w ->
    AddressInfo ->
    f (Classif s w)
  ) ->
  Ctx lhs sys v Void ->
  AnalyzerInput OptionTypes t v ->
  Maybe (f (Classif t v))
typetrick fromType h gamma inputT = fmap unboxClassif <$> analyze TokenTypes fromType
  (\ wkn gamma inputS addressInfo -> BoxClassif <$> h wkn gamma inputS addressInfo)
  gamma inputT
