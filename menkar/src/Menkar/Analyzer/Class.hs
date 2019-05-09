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
import Data.Functor.Compose
import GHC.Generics

data AnalyzerOption = OptionSubASTs | OptionTypes | OptionRelate
data AnalyzerToken (option :: AnalyzerOption) where
  TokenSubASTs :: AnalyzerToken OptionSubASTs
  TokenTypes :: AnalyzerToken OptionTypes
  TokenRelate :: AnalyzerToken OptionRelate

data AnalyzableToken sys (ast :: * -> *) where
  AnTokenModedModality :: AnalyzableToken sys (ModedModality sys)
  AnTokenBinding :: (Analyzable sys (rhs sys)) =>
    AnalyzableToken sys (rhs sys) -> AnalyzableToken sys (Binding Type rhs sys)
  AnTokenClassifBinding :: (Analyzable sys rhs) =>
    AnalyzableToken sys rhs -> AnalyzableToken sys (ClassifBinding Type rhs sys)
  AnTokenUniHSConstructor :: AnalyzableToken sys (UniHSConstructor sys)
  AnTokenConstructorTerm :: AnalyzableToken sys (ConstructorTerm sys)
  AnTokenType :: AnalyzableToken sys (Type sys)
  AnTokenDependentEliminator :: AnalyzableToken sys (DependentEliminator sys)
  AnTokenEliminator :: AnalyzableToken sys (Eliminator sys)
  AnTokenTermNV :: AnalyzableToken sys (TermNV sys)
  AnTokenTerm :: AnalyzableToken sys (Term sys)
  AnTokenDeclaration :: (Analyzable sys (rhs sys)) =>
    AnalyzableToken sys (rhs sys) -> AnalyzableToken sys (Declaration declSort rhs sys)
  AnTokenTelescoped :: (Analyzable sys (rhs sys)) =>
    AnalyzableToken sys (rhs sys) -> AnalyzableToken sys (Telescoped Type rhs sys)
  AnTokenValRHS :: AnalyzableToken sys (ValRHS sys)
  AnTokenModuleRHS :: AnalyzableToken sys (ModuleRHS sys)
  AnTokenEntry :: AnalyzableToken sys (Entry sys)
  AnTokenU1 :: AnalyzableToken sys U1
  AnTokenPair1 :: (Analyzable sys f, Analyzable sys g) =>
    AnalyzableToken sys f -> AnalyzableToken sys g -> AnalyzableToken sys (f :*: g)
  --AnTokenCompose :: AnalyzableToken sys t -> AnalyzableToken sys (Compose f t)

data AnalyzerError sys =
  AnErrorTermMeta |
  AnErrorTermWildcard |
  AnErrorTermQName |
  AnErrorTermAlreadyChecked |
  AnErrorTermAlgorithm |
  AnErrorTermSys {- insert system error here -} |
  AnErrorTermProblem |
  AnErrorVar

newtype BoxClassif t v = BoxClassif {unboxClassif :: Classif t v}

data ClassifInfo a = ClassifMustBe a | ClassifWillBe a | {-| Not allowed for terms. -} ClassifUnknown
  deriving (Functor, Foldable, Traversable)

classifMust2will :: ClassifInfo a -> ClassifInfo a
classifMust2will (ClassifMustBe a) = ClassifWillBe a
classifMust2will ca = ca
fromClassifInfo :: a -> ClassifInfo a -> a
fromClassifInfo a0 (ClassifMustBe a) = a
fromClassifInfo a0 (ClassifWillBe a) = a
fromClassifInfo a0 (ClassifUnknown) = a0

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
  {-| If true, a classifier must be provided or at least propagated downward. -}
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
class (Functor t, Functor (Relation t), Analyzable sys (Classif t)) => Analyzable sys t where
  type AnalyzerExtraInput t :: * -> *
  type Classif t :: * -> *
  type Relation t :: * -> *
  analyzableToken :: AnalyzableToken sys t
  analyze :: forall option lhs f v .
    (Applicative f, DeBruijnLevel v, Traversable (lhs sys), Analyzable sys (Classif t)) =>
    AnalyzerToken option ->
    {-| For adding stuff to the context. -}
    (forall w . Type sys w -> lhs sys w) ->
    Ctx lhs sys v Void ->
    AnalyzerInput option t v ->
    (forall s w .
      (Analyzable sys s, Analyzable sys (Classif s), DeBruijnLevel w) =>
      (v -> w) ->
      Ctx lhs sys w Void ->
      AnalyzerInput option s w ->
      AddressInfo ->
      (t v -> Maybe (s w)) ->
      f (AnalyzerResult option s w)
    ) ->
    Either (AnalyzerError sys) (f (AnalyzerResult option t v))
  -- | The conversion relation, used to compare expected and actual classifier.
  -- | The token is only given to pass Haskell's ambiguity check.
  convRel :: AnalyzableToken sys t -> Mode sys v -> Relation (Classif t) v

subASTsTyped :: forall sys f t v .
  (Applicative f, Analyzable sys t, Analyzable sys (Classif t), DeBruijnLevel v, SysTrav sys) =>
  Ctx Type sys v Void ->
  AnalyzerInput OptionSubASTs t v ->
  (forall s w .
    (Analyzable sys s, Analyzable sys (Classif s), DeBruijnLevel w) =>
    (v -> w) ->
    Ctx Type sys w Void ->
    AnalyzerInput OptionSubASTs s w ->
    AddressInfo ->
    f (s w)
  ) ->
  Either (AnalyzerError sys) (f (t v))
subASTsTyped gamma inputT h = fmap unbox1 <$> (analyze TokenSubASTs id gamma inputT $
  \ wkn gamma inputS addressInfo _ -> Box1 <$> h wkn gamma inputS addressInfo
  )
  
subASTs :: forall sys f t v .
  (Applicative f, Analyzable sys t, Analyzable sys (Classif t), DeBruijnLevel v, SysTrav sys) =>
  Ctx Type sys v Void ->
  t v ->
  AnalyzerExtraInput t v ->
  (forall s w .
    (Analyzable sys s, Analyzable sys (Classif s), DeBruijnLevel w) =>
    (v -> w) ->
    Ctx Type sys w Void ->
    s w ->
    AnalyzerExtraInput s w ->
    AddressInfo ->
    f (s w)
  ) ->
  Either (AnalyzerError sys) (f (t v))
subASTs gamma t extraInputT h = subASTsTyped gamma (AnalyzerInput t extraInputT ClassifUnknown IfRelateSubASTs) $
  \ wkn gamma inputS addressInfo ->
     h wkn gamma (_analyzerInput'get inputS) (_analyzerInput'extra inputS) addressInfo
  
typetrick :: forall sys lhs f t v .
  (Applicative f, Analyzable sys t, Analyzable sys (Classif t), DeBruijnLevel v, Traversable (lhs sys)) =>
  (forall w . Type sys w -> lhs sys w) ->
  Ctx lhs sys v Void ->
  AnalyzerInput OptionTypes t v ->
  (forall s w .
    (Analyzable sys s, Analyzable sys (Classif s), DeBruijnLevel w) =>
    (v -> w) ->
    Ctx lhs sys w Void ->
    AnalyzerInput OptionTypes s w ->
    AddressInfo ->
    f (Classif s w)
  ) ->
  Either (AnalyzerError sys) (f (Classif t v))
typetrick fromType gamma inputT h = fmap unboxClassif <$> (analyze TokenTypes fromType gamma inputT $
  \ wkn gamma inputS addressInfo _ -> BoxClassif <$> h wkn gamma inputS addressInfo
  )
