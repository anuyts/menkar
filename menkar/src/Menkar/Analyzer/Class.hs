{-# LANGUAGE AllowAmbiguousTypes, UndecidableInstances #-}

module Menkar.Analyzer.Class where

import Menkar.Basic.Context
import Menkar.Fine.Syntax
import Menkar.Fine.Context

import Data.Functor.Coerce
import Data.Omissible
import Data.Constraint.Witness
import Data.Constraint.Conditional
import Control.Exception.AssertFalse

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
  _analyzerInput'get1 :: t v,
  -- | Needs to be present when calling @'analyze'@.
  _analyzerInput'get2 :: IfRelate option (Maybe (t v)),
  _analyzerInput'extra1 :: AnalyzerExtraInput t v,
  _analyzerInput'extra2 :: IfRelate option (AnalyzerExtraInput t v),
  _analyzerInput'classifInfo :: ClassifInfo (Classif t v, IfRelate option (Classif t v)),
  _analyzerInput'relation :: IfRelate option (Relation t v)}

mapMaybeClassifs :: forall option s t w v .
  (s w -> t v) ->
  ClassifInfo (s w, IfRelate option (s w)) ->
  ClassifInfo (t v, IfRelate option (t v))
mapMaybeClassifs f = fmap (bimap f $ fmap f)

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

type family VarClassif (option :: AnalyzerOption) :: KSys -> * -> *
type instance VarClassif OptionSubASTs = Type
type instance VarClassif OptionTypes = Type
type instance VarClassif OptionRelate = Twice2 Type

type family CheckRelate (option :: AnalyzerOption) :: Bool
type instance CheckRelate OptionSubASTs = False
type instance CheckRelate OptionTypes = False
type instance CheckRelate OptionRelate = True

class (Functor (VarClassif option sys)) => IsAnalyzerOption option sys where
instance (SysTrav sys) => IsAnalyzerOption OptionSubASTs sys where
instance (SysTrav sys) => IsAnalyzerOption OptionTypes sys where
instance (SysTrav sys) => IsAnalyzerOption OptionRelate sys where

toVarClassif :: forall option sys v .
  AnalyzerToken option ->
  Type sys v ->
  IfRelate option (Type sys v) ->
  VarClassif option sys v
toVarClassif option ty1 (Conditional ty2) = case option of
  TokenSubASTs -> ty1
  TokenTypes -> ty1
  TokenRelate -> Twice2 ty1 ty2

type IfRelate option = Conditional (option ~ OptionRelate)

absurdRelate :: (CheckRelate option ~ False) => IfRelate option a
absurdRelate = Conditional unreachable

{-
data IfRelate (option :: AnalyzerOption) a where
  IfRelateSubASTs :: IfRelate OptionSubASTs a
  IfRelateTypes :: IfRelate OptionTypes a
  IfRelate :: a -> IfRelate OptionRelate a

deriving instance Functor (IfRelate option)
-}

toIfRelate :: AnalyzerToken option -> a -> IfRelate option a
toIfRelate option = return
{-
toIfRelate TokenSubASTs a = IfRelateSubASTs
toIfRelate TokenTypes a = IfRelateTypes
toIfRelate TokenRelate a = IfRelate a
-}

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
  analyzableToken :: AnalyzableToken sys t
  witClassif :: AnalyzableToken sys t -> Witness (Analyzable sys (Classif t))
  analyze :: forall option f v .
    (Applicative f, DeBruijnLevel v, IsAnalyzerOption option sys) =>
    AnalyzerToken option ->
    --{-| When AST-nodes do not have the same head. -}
    --(forall a . IfRelate option (f a)) ->
    {-| For adding stuff to the context. -}
    Ctx (VarClassif option) sys v Void ->
    AnalyzerInput option t v ->
    (forall s w .
      (Analyzable sys s, DeBruijnLevel w) =>
      (v -> w) ->
      Ctx (VarClassif option) sys w Void ->
      AnalyzerInput option s w ->
      AddressInfo ->
      (t v -> Maybe (s w)) ->
      f (AnalyzerResult option s w)
    ) ->
    Either (AnalyzerError sys) (f (AnalyzerResult option t v))
  -- | The conversion relation, used to compare expected and actual classifier.
  -- | The token is only given to pass Haskell's ambiguity check.
  convRel :: AnalyzableToken sys t -> Mode sys v -> Relation (Classif t) v
  extraClassif :: AnalyzerExtraInput (Classif t) v

haveClassif :: forall sys t a . (Analyzable sys t) => (Analyzable sys (Classif t) => a) -> a
haveClassif a = have (witClassif (analyzableToken :: AnalyzableToken sys t)) a

subASTsTyped :: forall sys f t v .
  (Applicative f, Analyzable sys t, DeBruijnLevel v, SysTrav sys) =>
  Ctx Type sys v Void ->
  AnalyzerInput OptionSubASTs t v ->
  (forall s w .
    (Analyzable sys s, DeBruijnLevel w) =>
    (v -> w) ->
    Ctx Type sys w Void ->
    AnalyzerInput OptionSubASTs s w ->
    AddressInfo ->
    f (s w)
  ) ->
  Either (AnalyzerError sys) (f (t v))
subASTsTyped gamma inputT h = fmap unbox1 <$> (analyze TokenSubASTs gamma inputT $
  \ wkn gamma inputS addressInfo _ -> Box1 <$> h wkn gamma inputS addressInfo
  )
  
subASTs :: forall sys f t v .
  (Applicative f, Analyzable sys t, DeBruijnLevel v, SysTrav sys) =>
  Ctx Type sys v Void ->
  t v ->
  AnalyzerExtraInput t v ->
  (forall s w .
    (Analyzable sys s, DeBruijnLevel w) =>
    (v -> w) ->
    Ctx Type sys w Void ->
    s w ->
    AnalyzerExtraInput s w ->
    AddressInfo ->
    f (s w)
  ) ->
  Either (AnalyzerError sys) (f (t v))
subASTs gamma t extraInputT h = subASTsTyped gamma
  (AnalyzerInput t absurdRelate extraInputT absurdRelate ClassifUnknown absurdRelate) $
  \ wkn gamma inputS addressInfo ->
     h wkn gamma (_analyzerInput'get1 inputS) (_analyzerInput'extra1 inputS) addressInfo
  
typetrick :: forall sys f t v .
  (Applicative f, Analyzable sys t, DeBruijnLevel v, SysTrav sys) =>
  Ctx Type sys v Void ->
  AnalyzerInput OptionTypes t v ->
  (forall s w .
    (Analyzable sys s, DeBruijnLevel w) =>
    (v -> w) ->
    Ctx Type sys w Void ->
    AnalyzerInput OptionTypes s w ->
    AddressInfo ->
    f (Classif s w)
  ) ->
  Either (AnalyzerError sys) (f (Classif t v))
typetrick gamma inputT h = fmap unboxClassif <$> (analyze TokenTypes gamma inputT $
  \ wkn gamma inputS addressInfo _ -> BoxClassif <$> h wkn gamma inputS addressInfo
  )
