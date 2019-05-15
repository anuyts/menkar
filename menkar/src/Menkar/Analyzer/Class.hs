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
import Data.Maybe

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

{-
data AnalyzerInput (option :: AnalyzerOption) (t :: * -> *) (v :: *) = AnalyzerInput {
  _analyzerInput'get1 :: t v,
  -- -- | Needs to be present when calling @'analyze'@.
  --_analyzerInput'get2 :: IfRelate option (Maybe (t v)),
  _analyzerInput'extra1 :: AnalyzerExtraInput t v,
  _analyzerInput'extra2 :: IfRelate option (AnalyzerExtraInput t v),
  _analyzerInput'classifInfo :: ClassifInfo (Classif t v, IfRelate option (Classif t v)),
  _analyzerInput'relation :: IfRelate option (Relation t v)}
-}

data AnalyzerInput (option :: AnalyzerOption) (t :: * -> *) (v :: *) = AnalyzerInput {
  _analyzerInput'get :: t v,
  _analyzerInput'extra :: AnalyzerExtraInput t v,
  _analyzerInput'classifInfo :: ClassifInfo (Classif t v)}
deriving instance (Functor t,
                   Functor (AnalyzerExtraInput t),
                   Functor (Classif t))
  => Functor (AnalyzerInput option t)

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
toVarClassif option ty1 (ConditionalT identityTy2) = case option of
  TokenSubASTs -> ty1
  TokenTypes -> ty1
  TokenRelate -> Twice2 ty1 (runIdentity identityTy2)

type IfRelateT option m = ConditionalT (option ~ OptionRelate) m
type IfRelate option = IfRelateT option Identity

absurdRelateT :: (CheckRelate option ~ False) => IfRelateT option m a
absurdRelateT = ConditionalT $ return unreachable
absurdRelate :: (CheckRelate option ~ False) => IfRelate option a
absurdRelate = absurdRelateT -- conditional unreachable

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

class (Functor t,
       Functor (AnalyzerExtraInput t),
       Functor (Classif t),
       Functor (Relation t)) => Analyzable sys t where
  type AnalyzerExtraInput t :: * -> *
  type Classif t :: * -> *
  type Relation t :: * -> *
  analyzableToken :: AnalyzableToken sys t
  witClassif :: AnalyzableToken sys t -> Witness (Analyzable sys (Classif t))
  analyze :: forall option f v .
    (Applicative f, DeBruijnLevel v, IsAnalyzerOption option sys) =>
    AnalyzerToken option ->
    Ctx (VarClassif option) sys v Void ->
    AnalyzerInput option t v ->
    (forall s ext . (Analyzable sys s, DeBruijnLevel (ext v), Traversable ext) =>
      (forall u . (DeBruijnLevel u, DeBruijnLevel (ext u)) => u -> ext u) ->
      (forall u . (DeBruijnLevel u, DeBruijnLevel (ext u)) => 
        AnalyzerInput option t u ->
        Maybe (AnalyzerInput option s (ext u))
      ) ->
      (forall u . (DeBruijnLevel u, DeBruijnLevel (ext u)) =>
        Ctx (VarClassif option) sys u Void ->
        AnalyzerInput option t u ->
        IfRelate option (AnalyzerInput option t u) ->
        Maybe (Ctx (VarClassif option) sys (ext u) Void)
      ) ->
      (forall u . (DeBruijnLevel u, DeBruijnLevel (ext u)) =>
        Relation t u -> Relation s (ext u)
      ) ->
      AddressInfo ->
      f (AnalyzerResult option s (ext v))
    ) ->
    Either (AnalyzerError sys) (f (AnalyzerResult option t v))
  -- | The conversion relation, used to compare expected and actual classifier.
  -- | The token is only given to pass Haskell's ambiguity check.
  convRel :: AnalyzableToken sys t -> Mode sys v -> Relation (Classif t) v
  extraClassif :: AnalyzerExtraInput (Classif t) v

extCtxId :: forall sys t option u option' . (DeBruijnLevel u) => 
        Ctx (VarClassif option') sys u Void ->
        AnalyzerInput option t u ->
        IfRelate option' (AnalyzerInput option t u) ->
        Maybe (Ctx (VarClassif option') sys (Identity u) Void)
extCtxId gamma _ _ = Just $ CtxId gamma

haveClassif :: forall sys t a . (Analyzable sys t) => (Analyzable sys (Classif t) => a) -> a
haveClassif a = have (witClassif (analyzableToken :: AnalyzableToken sys t)) a

makeLenses ''AnalyzerInput


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
analyzeOld :: forall sys t option f v .
    (Analyzable sys t, Applicative f, DeBruijnLevel v, IsAnalyzerOption option sys) =>
    AnalyzerToken option ->
    --{-| When AST-nodes do not have the same head. -}
    --(forall a . IfRelate option (f a)) ->
    {-| For adding stuff to the context. -}
    Ctx (VarClassif option) sys v Void ->
    AnalyzerInput option t v ->
    IfRelate option (AnalyzerInput option t v) ->
    IfRelate option (Relation t v) ->
    (forall s w .
      (Analyzable sys s, DeBruijnLevel w) =>
      (v -> w) ->
      Maybe (Ctx (VarClassif option) sys w Void) ->
      AnalyzerInput option s w ->
      IfRelate option (Maybe (AnalyzerInput option s w)) ->
      IfRelate option (Relation s w) ->
      AddressInfo ->
      (t v -> Maybe (s w)) ->
      f (AnalyzerResult option s w)
    ) ->
    Either (AnalyzerError sys) (f (AnalyzerResult option t v))
analyzeOld token gamma inputT1 condInputT2 condRel h =
  analyze token gamma inputT1 $ \ wkn extractT extendCtx extractRel info ->
  h wkn
    (extendCtx gamma inputT1 condInputT2)
    (fromMaybe unreachable $ extractT inputT1)
    (extractT <$> condInputT2)
    (extractRel <$> condRel)
    info
    (\ t1' -> _analyzerInput'get <$> extractT (analyzerInput'get .~ t1' $ inputT1))

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
subASTsTyped gamma inputT h = fmap unbox1 <$>
  (analyzeOld TokenSubASTs gamma inputT absurdRelate absurdRelate $
    \ wkn maybeGamma inputS _ _ addressInfo _ ->
      Box1 <$> h wkn (fromMaybe unreachable maybeGamma) inputS addressInfo
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
  (AnalyzerInput t extraInputT ClassifUnknown) $
  \ wkn gamma inputS addressInfo ->
     h wkn gamma (_analyzerInput'get inputS) (_analyzerInput'extra inputS) addressInfo
  
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
typetrick gamma inputT h = fmap unboxClassif <$>
  (analyzeOld TokenTypes gamma inputT absurdRelate absurdRelate $
    \ wkn maybeGamma inputS _ _ addressInfo _ ->
      BoxClassif <$> h wkn (fromMaybe unreachable maybeGamma) inputS addressInfo
  )
