{-# LANGUAGE AllowAmbiguousTypes, UndecidableInstances #-}

module Menkar.Analyzer.Class where

import Menkar.Basic.Context
import Menkar.Fine.Syntax
import Menkar.Fine.Context
import Menkar.System.Fine

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

data AnalyzerOption = OptionTrav | OptionTC | OptionRel | OptionSolve

data AnalyzerToken (option :: AnalyzerOption) where
  TokenTrav :: AnalyzerToken OptionTrav
  TokenTC :: AnalyzerToken OptionTC
  TokenRel :: AnalyzerToken OptionRel
  TokenSolve :: AnalyzerToken OptionSolve

data AnalyzableToken sys (ast :: * -> *) where
  AnTokenModedModality :: AnalyzableToken sys (ModedModality sys)
  AnTokenBinding :: (Analyzable sys (rhs sys), ClassifExtraInput (rhs sys) ~ U1) =>
    AnalyzableToken sys (rhs sys) -> AnalyzableToken sys (Binding Type rhs sys)
  AnTokenClassifBinding :: (Analyzable sys rhs) =>
    AnalyzableToken sys rhs -> AnalyzableToken sys (ClassifBinding Type rhs sys)
  AnTokenNamedBinding :: (Analyzable sys (rhs sys)) =>
    AnalyzableToken sys (rhs sys) -> AnalyzableToken sys (NamedBinding rhs sys)
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
  AnTokenSys :: SysAnalyzableToken sys t -> AnalyzableToken sys t
  --AnTokenCompose :: AnalyzableToken sys t -> AnalyzableToken sys (Compose f t)

data AnalyzerError sys =
  AnErrorTermMeta |
  AnErrorTermWildcard |
  AnErrorTermQName |
  AnErrorTermAlreadyChecked |
  AnErrorTermAlgorithm |
  AnErrorTermSys (SysAnalyzerError sys) |
  AnErrorTermProblem |
  AnErrorVar

--newtype BoxClassif t v = BoxClassif {unboxClassif :: Classif t v}

data ClassifInfo a = ClassifMustBe a | ClassifWillBe a | {-| Not allowed for terms. -} ClassifUnknown
  deriving (Functor, Foldable, Traversable)
instance Applicative ClassifInfo where
  pure a = ClassifWillBe a
  ClassifMustBe f <*> ClassifMustBe a = ClassifMustBe $ f a
  ClassifMustBe f <*> ClassifWillBe a = ClassifMustBe $ f a
  ClassifWillBe f <*> ClassifMustBe a = ClassifMustBe $ f a
  ClassifWillBe f <*> ClassifWillBe a = ClassifWillBe $ f a
  ClassifUnknown <*> _ = ClassifUnknown
  _ <*> ClassifUnknown = ClassifUnknown

classifMust2will :: ClassifInfo a -> ClassifInfo a
classifMust2will (ClassifMustBe a) = ClassifWillBe a
classifMust2will ca = ca
fromClassifInfo :: a -> ClassifInfo a -> a
fromClassifInfo a0 (ClassifMustBe a) = a
fromClassifInfo a0 (ClassifWillBe a) = a
fromClassifInfo a0 (ClassifUnknown) = a0

{-
data AnalyzerInput (option :: AnalyzerOption) (t :: * -> *) (v :: *) = AnalyzerInput {
  _classification'get1 :: t v,
  -- -- | Needs to be present when calling @'analyze'@.
  --_classification'get2 :: IfDoubled option (Maybe (t v)),
  _classification'extra1 :: ClassifExtraInput t v,
  _classification'extra2 :: IfDoubled option (ClassifExtraInput t v),
  _classification'classifInfo :: ClassifInfo (Classif t v, IfDoubled option (Classif t v)),
  _classification'relation :: IfDoubled option (Relation t v)}
-}

data Classification (t :: * -> *) (v :: *) = Classification {
  _classification'get :: t v,
  _classification'extra :: ClassifExtraInput t v,
  _classification'classifInfo :: ClassifInfo (Classif t v)}
deriving instance (Functor t,
                   Functor (ClassifExtraInput t),
                   Functor (Classif t))
  => Functor (Classification t)

mapMaybeClassifs :: forall option s t w v .
  (s w -> t v) ->
  ClassifInfo (s w, IfDoubled option (s w)) ->
  ClassifInfo (t v, IfDoubled option (t v))
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

{-
type family AnalyzerResult (option :: AnalyzerOption) = (result :: (* -> *) -> * -> *) | result -> option
type instance AnalyzerResult OptionTrav = Box1
type instance AnalyzerResult OptionTC = BoxClassif
type instance AnalyzerResult OptionRel = Unit2
-}

data Analysis (option :: AnalyzerOption) (t :: * -> *) (vOrig :: *) (v :: *) where
  AnalysisTrav :: forall t vOrig v . t v -> Analysis OptionTrav t vOrig v
  AnalysisTC :: forall t vOrig v . Classif t v -> Analysis OptionTC t vOrig v
  AnalysisRel :: Analysis OptionRel t vOrig v
  AnalysisSolve :: forall t vOrig v . t vOrig -> Analysis OptionSolve t vOrig v

getAnalysisTrav :: forall t vOrig v . Analysis OptionTrav t vOrig v -> t v
getAnalysisTrav (AnalysisTrav t) = t
getAnalysisTC :: forall t vOrig v . Analysis OptionTC t vOrig v -> Classif t v
getAnalysisTC (AnalysisTC ct) = ct
getAnalysisSolve :: forall t vOrig v . Analysis OptionSolve t vOrig v -> t vOrig
getAnalysisSolve (AnalysisSolve tOrig) = tOrig

instance (Functor t, Functor (Classif t)) => Bifunctor (Analysis option t) where
  bimap fOrig f (AnalysisTrav t) = AnalysisTrav $ f <$> t
  bimap fOrig f (AnalysisTC ct) = AnalysisTC $ f <$> ct
  bimap fOrig f AnalysisRel = AnalysisRel
  bimap fOrig f (AnalysisSolve t) = AnalysisSolve $ fOrig <$> t
instance (Functor t, Functor (Classif t)) => Functor (Analysis option t vOrig) where
  fmap f analysis = bimap id f analysis

{-
type family TypeForOption (option :: AnalyzerOption) :: KSys -> * -> *
type instance TypeForOption OptionTrav = Type
type instance TypeForOption OptionTC = Type
type instance TypeForOption OptionRel = Twice2 Type
-}

type family TypeMaybeTwice (doubled :: Bool) :: KSys -> * -> *
type instance TypeMaybeTwice False = Type
type instance TypeMaybeTwice True = Twice2 Type
type TypeForOption (option :: AnalyzerOption) = TypeMaybeTwice (CheckDoubled option)

type family CheckDoubled (option :: AnalyzerOption) :: Bool
type instance CheckDoubled OptionTrav = False
type instance CheckDoubled OptionTC = False
type instance CheckDoubled OptionRel = True
type instance CheckDoubled OptionSolve = True

class (Functor (TypeForOption option sys)) => IsAnalyzerOption option sys where
instance (SysTrav sys) => IsAnalyzerOption OptionTrav sys where
instance (SysTrav sys) => IsAnalyzerOption OptionTC sys where
instance (SysTrav sys) => IsAnalyzerOption OptionRel sys where

toTypeForOption :: forall option sys v .
  AnalyzerToken option ->
  Type sys v ->
  IfDoubled option (Type sys v) ->
  TypeForOption option sys v
toTypeForOption option ty1 (ConditionalT identityTy2) = case option of
  TokenTrav -> ty1
  TokenTC -> ty1
  TokenRel -> Twice2 ty1 (runIdentity identityTy2)
  TokenSolve -> Twice2 ty1 (runIdentity identityTy2)

type IfDoubledT option m = ConditionalT (CheckDoubled option ~ True) m
type IfDoubled option = IfDoubledT option Identity

typesArentDoubledT :: forall doubled m a . (doubled ~ False) => ConditionalT (doubled ~ True) m a
typesArentDoubledT = ConditionalT $ return unreachable
typesArentDoubled :: forall doubled a . (doubled ~ False) => Conditional (doubled ~ True) a
typesArentDoubled = typesArentDoubledT -- conditional unreachable

{-
data IfDoubled (option :: AnalyzerOption) a where
  IfDoubledTrav :: IfDoubled OptionTrav a
  IfDoubledTC :: IfDoubled OptionTC a
  IfDoubled :: a -> IfDoubled OptionRel a

deriving instance Functor (IfDoubled option)
-}

toIfDoubled :: AnalyzerToken option -> a -> IfDoubled option a
toIfDoubled option = return
{-
toIfDoubled TokenTrav a = IfDoubledTrav
toIfDoubled TokenTC a   = IfDoubledTC
toIfDoubled TokenRel a  = IfDoubled a
-}

class (Functor t,
       Functor (ClassifExtraInput t),
       Functor (Classif t),
       Functor (Relation t)) => Analyzable sys t where
  type ClassifExtraInput t :: * -> *
  type Classif t :: * -> *
  type Relation t :: * -> *
  analyzableToken :: AnalyzableToken sys t
  witClassif :: AnalyzableToken sys t -> Witness (Analyzable sys (Classif t))
  analyze :: forall option f vOrig v .
    (Applicative f, DeBruijnLevel vOrig, DeBruijnLevel v, IsAnalyzerOption option sys) =>
    AnalyzerToken option ->
    Ctx (TypeForOption option) sys v Void ->
    Classification t v ->
    (forall s ext .
      (Analyzable sys s, DeBruijnLevel (ext vOrig), DeBruijnLevel (ext v), Traversable ext) =>
      (forall u . (DeBruijnLevel u, DeBruijnLevel (ext u)) => u -> ext u) ->
      (forall u . (DeBruijnLevel u, DeBruijnLevel (ext u)) => 
        Ctx (TypeForOption option) sys u Void ->
        Classification t u ->
        Maybe (Classification s (ext u))
      ) ->
      (forall u . (DeBruijnLevel u, DeBruijnLevel (ext u)) =>
        Ctx (TypeForOption option) sys u Void ->
        Classification t u ->
        IfDoubled option (Classification t u) ->
        Maybe (Ctx (TypeForOption option) sys (ext u) Void)
      ) ->
      ({-forall u . (DeBruijnLevel u, DeBruijnLevel (ext u)) =>-}
        Relation t v -> Relation s (ext v)
      ) ->
      AddressInfo ->
      f (Analysis option s (ext vOrig) (ext v))
    ) ->
    Either (AnalyzerError sys) (f (Analysis option t vOrig v))
  -- | The conversion relation, used to compare expected and actual classifier.
  -- | The token is only given to pass Haskell's ambiguity check.
  convRel :: AnalyzableToken sys t -> Mode sys v -> Relation (Classif t) v
  extraClassif :: ClassifExtraInput (Classif t) v

extCtxId :: forall sys t option u option' . (DeBruijnLevel u) => 
        Ctx (TypeForOption option') sys u Void ->
        Classification t u ->
        IfDoubled option' (Classification t u) ->
        Maybe (Ctx (TypeForOption option') sys (Identity u) Void)
extCtxId gamma _ _ = Just $ CtxId gamma
crispExtCtxId :: forall sys t option u option' . (DeBruijnLevel u, Multimode sys) => 
        Ctx (TypeForOption option') sys u Void ->
        Classification t u ->
        IfDoubled option' (Classification t u) ->
        Maybe (Ctx (TypeForOption option') sys (Identity u) Void)
crispExtCtxId gamma _ _ = Just $ CtxId $ crispModedModality (ctx'mode gamma) :\\ gamma

haveClassif :: forall sys t a . (Analyzable sys t) => (Analyzable sys (Classif t) => a) -> a
haveClassif a = have (witClassif (analyzableToken :: AnalyzableToken sys t)) a

makeLenses ''Classification


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
analyzeOld :: forall sys t option f vOrig v .
    (Analyzable sys t, Applicative f, DeBruijnLevel vOrig, DeBruijnLevel v, IsAnalyzerOption option sys) =>
    AnalyzerToken option ->
    --{-| When AST-nodes do not have the same head. -}
    --(forall a . IfDoubled option (f a)) ->
    {-| For adding stuff to the context. -}
    Ctx (TypeForOption option) sys v Void ->
    Classification t v ->
    IfDoubled option (Classification t v) ->
    IfDoubled option (Relation t v) ->
    (forall s wOrig w .
      (Analyzable sys s, DeBruijnLevel wOrig, DeBruijnLevel w) =>
      (v -> w) ->
      Maybe (Ctx (TypeForOption option) sys w Void) ->
      Classification s w ->
      IfDoubled option (Maybe (Classification s w)) ->
      IfDoubled option (Relation s w) ->
      AddressInfo ->
      (t v -> Maybe (s w)) ->
      f (Analysis option s wOrig w)
    ) ->
    Either (AnalyzerError sys) (f (Analysis option t vOrig v))
analyzeOld token gamma inputT1 condInputT2 condRel h =
  analyze token gamma inputT1 $ \ wkn extractT extendCtx extractRel info ->
  h wkn
    (extendCtx gamma inputT1 condInputT2)
    (fromMaybe unreachable $ extractT gamma inputT1)
    (extractT gamma <$> condInputT2)
    (extractRel <$> condRel)
    info
    (\ t1' -> _classification'get <$> extractT gamma (classification'get .~ t1' $ inputT1))

subASTsTyped :: forall sys f t v .
  (Applicative f, Analyzable sys t, DeBruijnLevel v, SysTrav sys) =>
  Ctx Type sys v Void ->
  Classification t v ->
  (forall s w .
    (Analyzable sys s, DeBruijnLevel w) =>
    (v -> w) ->
    Ctx Type sys w Void ->
    Classification s w ->
    AddressInfo ->
    f (s w)
  ) ->
  Either (AnalyzerError sys) (f (t v))
subASTsTyped gamma inputT h = fmap getAnalysisTrav <$>
  (analyzeOld @sys @t @OptionTrav @f @v @v TokenTrav gamma inputT typesArentDoubled typesArentDoubled $
    \ wkn maybeGamma inputS _ _ addressInfo _ ->
      AnalysisTrav <$> h wkn (fromMaybe unreachable maybeGamma) inputS addressInfo
  )
 
subASTs :: forall sys f t v .
  (Applicative f, Analyzable sys t, DeBruijnLevel v, SysTrav sys) =>
  Ctx Type sys v Void ->
  t v ->
  ClassifExtraInput t v ->
  (forall s w .
    (Analyzable sys s, DeBruijnLevel w) =>
    (v -> w) ->
    Ctx Type sys w Void ->
    s w ->
    ClassifExtraInput s w ->
    AddressInfo ->
    f (s w)
  ) ->
  Either (AnalyzerError sys) (f (t v))
subASTs gamma t extraInputT h = subASTsTyped gamma
  (Classification t extraInputT ClassifUnknown) $
  \ wkn gamma inputS addressInfo ->
     h wkn gamma (_classification'get inputS) (_classification'extra inputS) addressInfo
  
typetrick :: forall sys f t v .
  (Applicative f, Analyzable sys t, DeBruijnLevel v, SysTrav sys) =>
  Ctx Type sys v Void ->
  Classification t v ->
  (forall s w .
    (Analyzable sys s, DeBruijnLevel w) =>
    (v -> w) ->
    Ctx Type sys w Void ->
    Classification s w ->
    AddressInfo ->
    f (Classif s w)
  ) ->
  Either (AnalyzerError sys) (f (Classif t v))
typetrick gamma inputT h = fmap getAnalysisTC <$>
  (analyzeOld @sys @t @OptionTC @f @v @v TokenTC gamma inputT typesArentDoubled typesArentDoubled $
    \ wkn maybeGamma inputS _ _ addressInfo _ ->
      AnalysisTC <$> h wkn (fromMaybe unreachable maybeGamma) inputS addressInfo
  )
