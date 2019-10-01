{- # LANGUAGE DataKinds, KindSignatures, GADTs, TypeOperators, RankNTypes, #-}
{-# LANGUAGE TemplateHaskell #-}

module Menkar.Fine.Syntax.Syntax where

import Menkar.System.Basic
import Menkar.System.Fine.Syntax
import Menkar.Fine.Syntax.Substitution hiding (Expr (..))
import Menkar.Basic.Context
import qualified Menkar.Raw.Syntax as Raw

import Data.Functor.Functor1
import Data.Omissible
import Data.Functor.Coyoneda.NF
import Control.DeepSeq.Redone
import Data.Constraint.Preimage
import Data.Constraint.Trivial

import GHC.Generics
import Data.Functor.Compose
import Data.Functor.Identity
import Data.Maybe
import Control.Exception.AssertFalse
import Control.Lens
import Data.Void
import Data.Kind hiding (Type)

type SysAST sys = SysSyntax (Term sys) sys

-------------------

data Twice2 t (a :: ka) (b :: kb) = Twice2 {fstTwice2 :: t a b, sndTwice2 :: t a b}
  deriving (Functor, Foldable, Traversable, Generic1, NFData_)
deriving instance (CanSwallow (Term sys) (t sys)) => CanSwallow (Term sys) (Twice2 t sys)

data Twice1 t (a :: ka) = Twice1 {fstTwice1 :: t a, sndTwice1 :: t a}
  deriving (Functor, Foldable, Traversable, Generic1, NFData_)
deriving instance (CanSwallow (Term sys) t) => CanSwallow (Term sys) (Twice1 t)

twice1to2 :: Twice1 (t sys) v -> Twice2 t sys v
twice1to2 (Twice1 a b) = Twice2 a b
mapTwice1 :: (a v -> b v) -> Twice1 a v -> Twice1 b v
mapTwice1 f (Twice1 a1 a2) = Twice1 (f a1) (f a2)
flipTwice1 :: Twice1 t v -> Twice1 t v
flipTwice1 (Twice1 t1 t2) = Twice1 t2 t1

-------------------
  
newtype Box2 t (a :: ka) (b :: kb) = Box2 {unbox2 :: t a b}
  deriving (Functor, Foldable, Traversable, Generic1)
  deriving newtype NFData_
deriving newtype instance (CanSwallow (Term sys) (t sys)) => CanSwallow (Term sys) (Box2 t sys)

newtype Box1 t (a :: ka) = Box1 {unbox1 :: t a}
  deriving (Functor, Foldable, Traversable, Generic1)
  deriving newtype NFData_
deriving newtype instance (CanSwallow (Term sys) t) => CanSwallow (Term sys) (Box1 t)

data Unit2 (a :: ka) (b :: kb) = Unit2
  deriving (Functor, Foldable, Traversable, Generic1, NFData_, Show)
deriving instance CanSwallow (Term sys) (Unit2 sys)

data Void2 (a :: ka) (b :: kb) = Void2 Void
  deriving (Functor, Foldable, Traversable, Generic1, NFData_)
deriving instance CanSwallow (Term sys) (Void2 sys)
absurd2 :: Void2 a b -> d
absurd2 (Void2 v) = absurd v

newtype Maybe2 t (a :: ka) (b :: kb) = Maybe2 (Compose Maybe (t a) b)
  deriving (Functor, Foldable, Traversable, Generic1)
  deriving newtype NFData_
deriving newtype instance (
    CanSwallow (Term sys) (t sys)
  ) =>
  CanSwallow (Term sys) (Maybe2 t sys)

data Pair2 s t (a :: ka) (b :: kb) = Pair2 {fst2 :: s a b, snd2 :: t a b}
  deriving (Functor, Foldable, Traversable, Generic1, NFData_)
deriving instance (CanSwallow (Term sys) (s sys), CanSwallow (Term sys) (t sys)) => CanSwallow (Term sys) (Pair2 s t sys)

newtype Const1 t sys v = Const1 {getConst1 :: t v}
  deriving (Functor, Foldable, Traversable, Generic1)
  deriving newtype NFData_
deriving newtype instance (CanSwallow (Term sys) t) => CanSwallow (Term sys) (Const1 t a)

{-
data Pair3 t (a :: ka) (b :: kb) (c :: kc) = Pair3 {fst3 :: t a b c, snd3 :: t a b c}
  deriving (Functor, Foldable, Traversable, Generic1)
deriving instance (CanSwallow (Term sys) (t sys)) => CanSwallow (Term sys) (Pair3 t sys)
  
data Box2 t (a :: ka) (b :: kb) (c :: kc) = Box2 {unbox3 :: t a b c}
  deriving (Functor, Foldable, Traversable, Generic1)
deriving instance (CanSwallow (Term sys) (t sys)) => CanSwallow (Term sys) (Box2 t sys)

data Unit2 (a :: ka) (b :: kb) (c :: kc) = Unit2
  deriving (Functor, Foldable, Traversagble, Generic1, Show)
deriving instance CanSwallow (Term sys) (Unit2 sys)

data Void2 (a :: ka) (b :: kb) (c :: kc) = Void2 Void
  deriving (Functor, Foldable, Traversable, Generic1)
deriving instance CanSwallow (Term sys) (Void2 sys)
absurd3 :: Void2 a b c -> d
absurd3 (Void2 v) = absurd v

data Unit1 (a :: ka) = Unit1
  deriving (Functor, Foldable, Traversable, Generic1, Show)
deriving instance CanSwallow (Term sys) (Unit1)

newtype Maybe2 t (a :: ka) (b :: kb) (c :: kc) = Maybe2 (Compose Maybe (t a b) c)
  deriving (Functor, Foldable, Traversable, Generic1)
deriving instance (
    CanSwallow (Term sys) mode,
    CanSwallow (Term sys) modty,
    CanSwallow (Term sys) (t sys)
  ) =>
  CanSwallow (Term sys) (Maybe2 t sys)
-}

-------------------

{- Segment info will have to depend on v, because 'resolves' annotations have variables -}
--data MetaInfo where

{-
data DependentModality (mode :: * -> *) (modty :: * -> *) (v :: *) =
  NonDependentModality (ModedModality sys v) | Flat (mode v)
  --DependentModality {dmodDom :: mode v, dmodCod :: mode (Maybe v), dmodMod :: modty v}
  deriving (Functor, Foldable, Traversable, Generic1)
LookupResult sys (VarOpenCtx v w)deriving instance (Functor mode, Functor modty, CanSwallow (Term sys) mode (Term sys), CanSwallow (Term sys) modty (Term sys)) =>
  CanSwallow (Term sys) (DependentModality sys) (Term sys)
-}

data ModRel = ModEq | ModLeq
  deriving (Generic, NFData)

type ModedModality sys = Modality sys
_modality'mod :: ModedModality sys v -> Modality sys v
_modality'mod mu = mu
{-
data ModedModality (sys :: KSys) (v :: *) =
  ModedModality {
    modality'dom :: Mode sys v,
    modality'cod :: Mode sys v,
    modality'mod :: Modality sys v}
deriving instance (SysTrav sys) => Functor (ModedModality sys)
deriving instance (SysTrav sys) => Foldable (ModedModality sys)
deriving instance (SysTrav sys) => Traversable (ModedModality sys)
deriving instance (SysTrav sys) => Generic1 (ModedModality sys)
deriving instance (SysSyntax (Term sys) sys) => CanSwallow (Term sys) (ModedModality sys)
-}

data ModalityTo sys v = ModalityTo {
  _modalityTo'dom :: Mode sys v,
  _modalityTo'mod :: Modality sys v
  }
  deriving (Generic1)
deriving instance (SysNF sys) => NFData_ (ModalityTo sys)
deriving instance (SysTrav sys) => Functor (ModalityTo sys)
deriving instance (SysTrav sys) => Foldable (ModalityTo sys)
deriving instance (SysTrav sys) => Traversable (ModalityTo sys)
deriving instance (SysSyntax (Term sys) sys) => CanSwallow (Term sys) (ModalityTo sys)

{-
data ModedContramodality (sys :: KSys) (v :: *) =
  ModedContramodality {contramodality'dom :: Mode sys v, contramodality'rightAdjoint :: Modality sys v}
deriving instance (SysTrav sys) => Functor (ModedContramodality sys)
deriving instance (SysTrav sys) => Foldable (ModedContramodality sys)
deriving instance (SysTrav sys) => Traversable (ModedContramodality sys)
deriving instance (SysTrav sys) => Generic1 (ModedContramodality sys)
deriving instance (SysSyntax (Term sys) sys) =>
  CanSwallow (Term sys) (ModedContramodality sys)
-}

type ModedDegree sys = Degree sys
_degree'deg :: ModedDegree sys v -> Degree sys v
_degree'deg deg = deg
{-
data ModedDegree (sys :: KSys) (v :: *) =
  ModedDegree {_degree'mode :: Mode sys v, _degree'deg :: Degree sys v}
deriving instance (SysTrav sys) => Functor (ModedDegree sys)
deriving instance (SysTrav sys) => Foldable (ModedDegree sys)
deriving instance (SysTrav sys) => Traversable (ModedDegree sys)
deriving instance (SysTrav sys) => Generic1 (ModedDegree sys)
deriving instance (SysSyntax (Term sys) sys) => CanSwallow (Term sys) (ModedDegree sys)
-}

{-| Looking up something the module @modul@ in @dmu :\\ (gamma :<...> modul)@ yields
    @LeftDivided (ctx'mode gamma) dmu _@.-}
data LeftDivided content (sys :: KSys) v = LeftDivided {
    _leftDivided'originalMode :: (Mode sys) v,
    _leftDivided'modality :: ModedModality sys v,
    _leftDivided'content :: content sys v}
deriving instance (SysTrav sys, Functor (content sys)) => Functor (LeftDivided content sys)
deriving instance (SysTrav sys, Foldable (content sys)) => Foldable (LeftDivided content sys)
deriving instance (SysTrav sys, Traversable (content sys)) => Traversable (LeftDivided content sys)
deriving instance Generic1 (LeftDivided content sys)
deriving instance (SysNF sys, NFData_ (content sys)) => NFData_ (LeftDivided content sys)
deriving instance (
    SysSyntax (Term sys) sys,
    Functor (content sys),
    CanSwallow (Term sys) (content sys)
  ) => CanSwallow (Term sys) (LeftDivided content sys)

data ModApplied content (sys :: KSys) v = ModApplied {
    _modApplied'modality :: ModedModality sys v,
    _modApplied'content :: content sys v}
deriving instance (SysTrav sys, Functor (content sys)) => Functor (ModApplied content sys)
deriving instance (SysTrav sys, Foldable (content sys)) => Foldable (ModApplied content sys)
deriving instance (SysTrav sys, Traversable (content sys)) => Traversable (ModApplied content sys)
deriving instance Generic1 (ModApplied content sys)
deriving instance (SysNF sys, NFData_ (content sys)) => NFData_ (ModApplied content sys)
deriving instance (
    SysSyntax (Term sys) sys,
    Functor (content sys),
    CanSwallow (Term sys) (content sys)
  ) => CanSwallow (Term sys) (ModApplied content sys)

data LookupResult (sys :: KSys) v =
  LookupResultVar v |
  LookupResultVal (LeftDivided (Telescoped Type ValRHS) sys v) |
  LookupResultNothing
deriving instance (SysTrav sys) => Functor (LookupResult sys)
deriving instance (SysTrav sys) => Foldable (LookupResult sys)
deriving instance (SysTrav sys) => Traversable (LookupResult sys)
deriving instance Generic1 (LookupResult sys)
deriving instance (SysTrav sys) => NFData_ (LookupResult sys)

{-
modedLeftAdjoint :: ModedModality sys v -> ModedContramodality sys v
modedLeftAdjoint (ModedModality dom cod mod) = (ModedContramodality cod dom mod)
modedRightAdjoint :: ModedContramodality sys v -> ModedModality sys v
modedRightAdjoint (ModedContramodality dom cod mod) = (ModedModality cod dom mod)
-}

------------------------------------

data Binding
    (lhs :: KSys -> * -> *)
    (rhs :: KSys -> * -> *)
    (sys :: KSys) (v :: *) =
  Binding {
    binding'segment :: Segment lhs sys v,
    binding'bodyFS :: FreeSwallow (Term sys) (rhs sys :.: VarExt) v
  }
deriving instance (SysTrav sys, Functor (lhs sys), Functor (rhs sys)) => Functor (Binding lhs rhs sys)
deriving instance (SysTrav sys, Foldable (lhs sys), Foldable (rhs sys)) => Foldable (Binding lhs rhs sys)
deriving instance (SysTrav sys, Traversable (lhs sys), Traversable (rhs sys)) => Traversable (Binding lhs rhs sys)
deriving instance (SysTrav sys, Functor (rhs sys)) => Generic1 (Binding lhs rhs sys)
deriving instance (SysTrav sys, NFData_ (lhs sys), NFData_ (rhs sys), Functor (rhs sys)) => NFData_ (Binding lhs rhs sys)
deriving instance (
    SysSyntax (Term sys) sys,
    Functor (lhs sys),
    Functor (rhs sys),
    CanSwallow (Term sys) (lhs sys),
    CanSwallow (Term sys) (rhs sys)
  ) => CanSwallow (Term sys) (Binding lhs rhs sys)
binding'bodyLowerFS :: (SysSyntax (Term sys) sys, Functor (rhs sys), CanSwallow (Term sys) (rhs sys)) =>
  Binding lhs rhs sys v -> rhs sys (VarExt v)
binding'bodyLowerFS = unComp1 . lowerFS . binding'bodyFS

{-
{-| Same as binding, but analyzer takes segment for granted and doesn't traverse it. -}
data ClassifBinding
    (lhs :: KSys -> * -> *)
    (rhs :: * -> *)
    (sys :: KSys) (v :: *) =
  ClassifBinding {
    _classifBinding'segment :: Segment lhs sys v,
    _classifBinding'body :: rhs (VarExt v)
  }
deriving instance (SysTrav sys, Functor (lhs sys), Functor (rhs)) => Functor (ClassifBinding lhs rhs sys)
deriving instance (SysTrav sys, Foldable (lhs sys), Foldable (rhs)) => Foldable (ClassifBinding lhs rhs sys)
deriving instance (SysTrav sys, Traversable (lhs sys), Traversable (rhs)) => Traversable (ClassifBinding lhs rhs sys)
deriving instance (SysTrav sys, Functor (lhs sys), Functor (rhs)) => Generic1 (ClassifBinding lhs rhs sys)
deriving instance (
    SysSyntax (Term sys) sys,
    Functor (lhs sys),
    Functor (rhs),
    CanSwallow (Term sys) (lhs sys),
    CanSwallow (Term sys) (rhs)
  ) => CanSwallow (Term sys) (ClassifBinding lhs rhs sys)
-}

data NamedBinding
    (rhs :: KSys -> * -> *)
    (sys :: KSys) (v :: *) =
  NamedBinding {
    _namedBinding'name :: Maybe Raw.Name,
    _namedBinding'bodyFS :: FreeSwallow (Term sys) (rhs sys :.: VarExt) v
  }
deriving instance (SysTrav sys, Functor (rhs sys)) => Functor (NamedBinding rhs sys)
deriving instance (SysTrav sys, Foldable (rhs sys)) => Foldable (NamedBinding rhs sys)
deriving instance (SysTrav sys, Traversable (rhs sys)) => Traversable (NamedBinding rhs sys)
deriving instance (SysTrav sys, Functor (rhs sys)) => Generic1 (NamedBinding rhs sys)
deriving instance (SysTrav sys, Functor (rhs sys), NFData_ (rhs sys)) => NFData_ (NamedBinding rhs sys)
deriving instance (
    SysSyntax (Term sys) sys,
    Functor (rhs sys),
    CanSwallow (Term sys) (rhs sys)
  ) => CanSwallow (Term sys) (NamedBinding rhs sys)
_namedBinding'bodyLowerFS :: (SysSyntax (Term sys) sys, Functor (rhs sys), CanSwallow (Term sys) (rhs sys)) =>
  NamedBinding rhs sys v -> rhs sys (VarExt v)
_namedBinding'bodyLowerFS = unComp1 . lowerFS . _namedBinding'bodyFS

newtype ModalBox (content :: KSys -> * -> *) (sys :: KSys) (v :: *) =
  ModalBox {_modalBox'content :: content sys v}
  deriving (Functor, Foldable, Traversable, Generic1)
  deriving newtype NFData_
deriving newtype instance (CanSwallow (Term sys) (content sys)) => CanSwallow (Term sys) (ModalBox content sys)
{-deriving instance (SysTrav sys, Functor (content sys)) => Functor (ModalBox content sys)
deriving instance (SysTrav sys, Foldable (content sys)) => Foldable (ModalBox content sys)
deriving instance (SysTrav sys, Traversable (content sys)) => Traversable (ModalBox content sys)
deriving instance (SysTrav sys, Functor (content sys)) => Generic1 (ModalBox content sys)
deriving instance (
    SysSyntax (Term sys) sys,
    Functor (content sys),
    CanSwallow (Term sys) (content sys)
  ) => CanSwallow (Term sys) (ModalBox content sys)
-}

------------------------------------

{-| Variables are stored in REVERSE order, i.e. in order of De Bruijn index. -}
newtype Dependencies (sys :: KSys) (v :: *) =
  Dependencies {getDependencies :: FreeSwallow (Term sys) (Compose [] (Mode sys :*: Term sys)) v}
deriving instance (SysTrav sys) => Functor (Dependencies sys)
deriving instance (SysTrav sys) => Foldable (Dependencies sys)
deriving instance (SysTrav sys) => Traversable (Dependencies sys)
deriving instance Generic1 (Dependencies sys)
deriving instance Generic (Dependencies sys v)
deriving anyclass instance (SysTrav sys) => Wrapped (Dependencies sys v)
deriving newtype instance (SysTrav sys) => NFData_ (Dependencies sys)
deriving newtype instance (SysSyntax (Term sys) sys) =>
  CanSwallow (Term sys) (Dependencies sys)

depcies2subst :: forall sys vOrig v . (SysAST sys, DeBruijnLevel vOrig) => Dependencies sys v -> vOrig -> Term sys v
depcies2subst (Dependencies depcies) vOrig = lowerFS $ hoistFS
  (\(Compose dts) -> snd1 (atVarRev vOrig dts))
  depcies

{-| HS-Types should carry no level information whatsoever:
    you couldn't type-check it, as they are definitionally irrelevant in the level.
-}
data UniHSConstructor (sys :: KSys) (v :: *) =
  UniHS {-^ Hofmann-Streicher universe, or at least a universe that classifies its own mode. -}
    (Mode sys v) {-^ mode (of both the universe and its elements) -}
    --(Term sys v) {-^ level it classifies -}
    |
  Pi (Binding Type Type sys v) |
  Sigma (Binding Type Type sys v) |
  EmptyType |
  UnitType |
  BoxType (Segment Type sys v) |
  NatType |
  EqType (Type sys v) (Term sys v) (Term sys v) |
  SysType (SysUniHSConstructor sys v)
deriving instance (SysTrav sys) => Functor (UniHSConstructor sys)
deriving instance (SysTrav sys) => Foldable (UniHSConstructor sys)
deriving instance (SysTrav sys) => Traversable (UniHSConstructor sys)
deriving instance Generic1 (UniHSConstructor sys)
deriving instance (SysTrav sys) => NFData_ (UniHSConstructor sys)
deriving instance (SysSyntax (Term sys) sys) =>
  CanSwallow (Term sys) (UniHSConstructor sys)

hs2term :: UniHSConstructor sys v -> Term sys v
hs2term ty = Expr2 $ TermCons $ ConsUniHS $ ty
hs2type :: UniHSConstructor sys v -> Type sys v
hs2type ty = Type $ Expr2 $ TermCons $ ConsUniHS $ ty
pattern TypeHS ty = Type (Expr2 (TermCons (ConsUniHS ty)))

data ConstructorTerm (sys :: KSys) (v :: *) =
  {-| element of the Hofmann-Streicher universe -}
  ConsUniHS
    --(mode v) {-^ Type's mode -}
    --(Term sys v) {-^ Type's unsafely assigned level -}
    (UniHSConstructor sys v) {-^ Type -} |
  Lam (Binding Type ValRHS sys v) |
  Pair
    (Binding Type Type sys v) {-^ pair's sigma type -} 
    (Term sys v)
    (Term sys v) |
  ConsUnit |
  ConsBox
    (Segment Type sys v) {-^ box's type -}
    (Term sys v) {-^ box's content -} |
  ConsZero |
  ConsSuc (Term sys v) |
  ConsRefl (Type sys v) (Term sys v)
deriving instance (SysTrav sys) => Functor (ConstructorTerm sys)
deriving instance (SysTrav sys) => Foldable (ConstructorTerm sys)
deriving instance (SysTrav sys) => Traversable (ConstructorTerm sys)
deriving instance Generic1 (ConstructorTerm sys)
deriving instance (SysTrav sys) => NFData_ (ConstructorTerm sys)
deriving instance (SysSyntax (Term sys) sys) =>
  CanSwallow (Term sys) (ConstructorTerm sys)

data SmartEliminator (sys :: KSys) (v :: *) =
  SmartElimDots |
  --SmartElimEnd Raw.ArgSpec |
  SmartElimArg Raw.ArgSpec (ModedModality sys v) (Term sys v) |
  SmartElimProj Raw.ProjSpec |
  SmartElimUnbox
deriving instance (SysTrav sys) => Functor (SmartEliminator sys)
deriving instance (SysTrav sys) => Foldable (SmartEliminator sys)
deriving instance (SysTrav sys) => Traversable (SmartEliminator sys)
deriving instance Generic1 (SmartEliminator sys)
deriving instance (SysTrav sys) => NFData_ (SmartEliminator sys)
deriving instance (SysSyntax (Term sys) sys) =>
  CanSwallow (Term sys) (SmartEliminator sys)

data DependentEliminator (sys :: KSys) (v :: *) =
  ElimSigma (NamedBinding (NamedBinding Term) sys v) |
  ElimBox (NamedBinding Term sys v) |
  ElimEmpty |
  ElimNat (Term sys v) (NamedBinding (NamedBinding Term) sys v)
deriving instance (SysTrav sys) => Functor (DependentEliminator sys)
deriving instance (SysTrav sys) => Foldable (DependentEliminator sys)
deriving instance (SysTrav sys) => Traversable (DependentEliminator sys)
deriving instance Generic1 (DependentEliminator sys)
deriving instance (SysTrav sys) => NFData_ (DependentEliminator sys)
deriving instance (SysSyntax (Term sys) sys) =>
  CanSwallow (Term sys) (DependentEliminator sys)

data Eliminator (sys :: KSys) (v :: *) =
  {-ElimUnsafeResize
    --(Term sys v) {-^ Type's unsafely assigned level -}
    {-(Term sys v) {-^ Type -}-} |-}
  App {
    _eliminator'argument :: (Term sys v)} |
  Fst |
  Snd |
  Unbox |
  Funext |
  ElimDep {
    _eliminator'motive :: (NamedBinding Type sys v),
    _eliminator'clauses :: DependentEliminator sys v} |
  ElimEq (NamedBinding (NamedBinding Type) sys v) (Term sys v)
deriving instance (SysTrav sys) => Functor (Eliminator sys)
deriving instance (SysTrav sys) => Foldable (Eliminator sys)
deriving instance (SysTrav sys) => Traversable (Eliminator sys)
deriving instance Generic1 (Eliminator sys)
deriving instance (SysTrav sys) => NFData_ (Eliminator sys)
deriving instance (SysSyntax (Term sys) sys) =>
  CanSwallow (Term sys) (Eliminator sys)

data Algorithm sys v =
  AlgGoal
    String {-^ goal's name -}
    (Compose [] (Term sys) v) {-^ dependencies, in reverse order -} |
  AlgSmartElim
    (Term sys v) {-^ eliminee -}
    (Compose [] (ModedModality sys :*: SmartEliminator sys) v)
      {-^ Eliminators. The moded modality inserted in front of a smart eliminator,
          is the composite of the modalities of that eliminator and the IMPLICIT eliminators immediately before it. -}
deriving instance (SysTrav sys) => Functor (Algorithm sys)
deriving instance (SysTrav sys) => Foldable (Algorithm sys)
deriving instance (SysTrav sys) => Traversable (Algorithm sys)
deriving instance Generic1 (Algorithm sys)
deriving instance (SysTrav sys) => NFData_ (Algorithm sys)
deriving instance (SysSyntax (Term sys) sys) =>
  CanSwallow (Term sys) (Algorithm sys)

newtype Type (sys :: KSys) (v :: *) = Type {unType :: Term sys v}
  {-ElType {-^ Constructor'ish -} 
    (UniHSConstructor sys v) {-^ Type -} |
  ElTerm {-^ Eliminator'ish -}
    (Term sys v) {-^ Type -}-}
deriving instance (SysTrav sys) => Functor (Type sys)
deriving instance (SysTrav sys) => Foldable (Type sys)
deriving instance (SysTrav sys) => Traversable (Type sys)
deriving instance Generic1 (Type sys)
deriving newtype instance (SysTrav sys) => NFData_ (Type sys)
deriving newtype instance (SysSyntax (Term sys) sys) =>
  CanSwallow (Term sys) (Type sys)

------------------------------------

data MetaNeutrality = MetaNeutral | MetaBlocked
  deriving (Eq, Generic, NFData)

data TermNV (sys :: KSys) (v :: *) =
  TermCons (ConstructorTerm sys v) |
  {-| It is an error to construct a @'TermNV'@ using @'TermElim'@ with an eliminator that
      doesn't match the SHAPE of the eliminee's type -}
  TermElim
    (ModalityTo sys v) {-^ modality by which the eliminee is used -}
    (Term sys v) {-^ eliminee -}
    (UniHSConstructor sys v) {-^ eliminee's type -}
    (Eliminator sys v) {-^ eliminator -} |
  {-| Boolean:  -}
  TermMeta
    MetaNeutrality
    Int {-^ Meta's index -}
    (Dependencies sys v) {-^ Dependencies -}
    (Compose Maybe (Algorithm sys) v) {-^ Human readable representation -} |
  TermWildcard {-^ A meta that need not be solved. -} |
  TermQName Raw.QName (FreeSwallow (Term sys) (LeftDivided (Telescoped Type ValRHS) sys) v) |
  TermAlreadyChecked (Term sys v) (Type sys v) {-^ Term that has already been checked and need not be checked again. -} |
  TermAlgorithm
    (Algorithm sys v)
    (Term sys v) {-^ result -} |
  {-TermSmartElim
    (Term sys v) {-^ eliminee -}
    (Compose [] (SmartEliminator sys) v) {-^ eliminators -}
    (Term sys v) {-^ result -} |
  TermGoal
    String {-^ goal's name -}
    (Compose [] (Term sys) v) {-^ dependencies -}
    (Term sys v) {-^ result -} |-}
  TermSys (SysTerm sys v) |
  TermProblem {-^ Wrapper of terms that make no sense. -}
    (Term sys v)
deriving instance (SysTrav sys) => Functor (TermNV sys)
deriving instance (SysTrav sys) => Foldable (TermNV sys)
deriving instance (SysTrav sys) => Traversable (TermNV sys)
deriving instance Generic1 (TermNV sys)
deriving instance (SysTrav sys) => NFData_ (TermNV sys)
deriving instance (SysSyntax (Term sys) sys) =>
  CanSwallow (Term sys) (TermNV sys)

type Term = Expr2 TermNV

isBlockedOrMeta :: Term sys v -> [Int] -> Bool
isBlockedOrMeta (Expr2 (TermMeta _ _ _ _)) _ = True
isBlockedOrMeta _ (_:_) = True
isBlockedOrMeta _ [] = False

------------------------------------

--data SegmentInfo = SegmentInfo {name :: String}

{-| Not used in segments. Used by the scoper, and also used for annotation entries. -}
data Annotation (sys :: KSys) v =
  AnnotMode (Mode sys v) |
  AnnotModality (Modality sys v) |
  AnnotImplicit |
  AnnotFlush Bool |
  AnnotLock
  --AnnotResolves (Term )
deriving instance (SysTrav sys) => Functor (Annotation sys)
deriving instance (SysTrav sys) => Foldable (Annotation sys)
deriving instance (SysTrav sys) => Traversable (Annotation sys)
deriving instance Generic1 (Annotation sys)
deriving instance (SysTrav sys) => NFData_ (Annotation sys)
deriving instance (SysSyntax (Term sys) sys) =>
  CanSwallow (Term sys) (Annotation sys)

data Annotations (sys :: KSys) v = Annotations {
  _annotations'dmu :: ModalityTo sys v,
  _annotations'plicity :: Compose Maybe (Plicity sys) v,
  _annotations'flush :: Maybe Bool,
  _annotations'lock :: Bool
  } deriving (Functor, Foldable, Traversable, Generic1, NFData_)
deriving instance (SysSyntax (Term sys) sys) =>
  CanSwallow (Term sys) (Annotations sys)

data Plicity (sys :: KSys) v =
  Explicit |
  Implicit |
  Resolves (Term sys v) -- this may change
deriving instance (SysTrav sys) => Functor (Plicity sys)
deriving instance (SysTrav sys) => Foldable (Plicity sys)
deriving instance (SysTrav sys) => Traversable (Plicity sys)
deriving instance Generic1 (Plicity sys)
deriving instance (SysTrav sys) => NFData_ (Plicity sys)
deriving instance (SysSyntax (Term sys) sys) =>
  CanSwallow (Term sys) (Plicity sys)

data DeclSort = DeclSortVal | DeclSortModule | DeclSortSegment -- -| DeclSortValSpec

{-
data DeclSortToken declSort where
  DeclSortTokenVal :: DeclSortToken DeclSortVal
  DeclSortTokenModule :: DeclSortToken DeclSortModule
  DeclSortTokenSegment :: DeclSortToken DeclSortSegment a
-}

data DeclName declSort where
  DeclNameVal :: Raw.Name -> DeclName DeclSortVal
  DeclNameModule :: String -> DeclName DeclSortModule
  DeclNameSegment :: Maybe Raw.Name -> DeclName DeclSortSegment
--  DeclNameValSpec :: DeclName DeclSortValSpec
instance NFData (DeclName declSort) where
  rnf (DeclNameVal name) = rnf name
  rnf (DeclNameModule str) = rnf str
  rnf (DeclNameSegment maybeName) = rnf maybeName

getDeclNameVal :: DeclName DeclSortVal -> Raw.Name
getDeclNameVal (DeclNameVal rawName) = rawName
getDeclNameModule :: DeclName DeclSortModule -> String
getDeclNameModule (DeclNameModule str) = str
getDeclNameSegment :: DeclName DeclSortSegment -> Maybe Raw.Name
getDeclNameSegment (DeclNameSegment maybeRawName) = maybeRawName

data DeclOptions = DeclOptions {
  _declOpts'flush :: Bool
  } deriving (Generic, NFData)
segOpts :: DeclOptions
segOpts = DeclOptions False
entryOpts :: DeclOptions
entryOpts = DeclOptions True

{-
data DeclType
     (declSort :: DeclSort)
     (mode :: * -> *)
     (modty :: * -> *)
     (v :: *) where
  DeclTypeVal :: Type sys v -> DeclType DeclSortVal sys v
  DeclTypeModule :: DeclType DeclSortModule sys v
  DeclTypeSegment :: (a -> Type sys v) -> DeclType (DeclSortSegment a) sys v  
-}

data Declaration
     {-| Type of the thing that lives in the context. Typically @'Type'@ or @'Pair3' 'Type'@ or some RHS-}
     (declSort :: DeclSort)
     (content :: KSys -> * -> *)
     (sys :: KSys)
     (v :: *) =
  Declaration {
    _decl'name :: DeclName declSort,
    --_decl'mode :: Mode sys v,
    _decl'modty :: ModalityTo sys v,
    _decl'plicity :: Plicity sys v,
    _decl'opts :: DeclOptions,
    _decl'content :: content sys v
  }
deriving instance (SysTrav sys, Functor (content sys)) => Functor (Declaration declSort content sys)
deriving instance (SysTrav sys, Foldable (content sys)) => Foldable (Declaration declSort content sys)
deriving instance (SysTrav sys, Traversable (content sys)) => Traversable (Declaration declSort content sys)
deriving instance Generic1 (Declaration declSort content sys)
deriving instance (SysTrav sys, NFData_ (content sys)) => NFData_ (Declaration declSort content sys)
deriving instance (
    SysSyntax (Term sys) sys,
    Functor (content sys),
    CanSwallow (Term sys) (content sys)
  ) => CanSwallow (Term sys) (Declaration declSort content sys)

--type TelescopedDeclaration declSort ty content = Telescoped ty (Declaration declSort content)
type Segment ty = Declaration DeclSortSegment ty

{-
_tdecl'name :: TelescopedDeclaration declSort ty content sys v -> DeclName declSort
_tdecl'name (Telescoped decl) = _decl'name decl
_tdecl'name (seg :|- tdecl) = _tdecl'name tdecl
_tdecl'name (mu :** tdecl) = _tdecl'name tdecl -}
_segment'name :: Segment ty sys v -> Maybe Raw.Name
_segment'name seg = case _decl'name seg of
  DeclNameSegment maybeName -> maybeName
_segment'content :: Segment ty sys v -> ty sys v
_segment'content = _decl'content
--_segment'mode :: Segment ty sys v -> Mode sys v
--_segment'mode = _decl'mode
_segment'modty :: Segment ty sys v -> ModalityTo sys v
_segment'modty = _decl'modty
_segment'plicity :: Segment ty sys v -> Plicity sys v
_segment'plicity = _decl'plicity

data Telescoped
     (ty :: KSys -> * -> *)
     (rhs :: KSys -> * -> *)
     (sys :: KSys)
     (v :: *) =
  Telescoped (rhs sys v) |
  Segment ty sys v :|- Telescoped ty rhs sys (VarExt v) |
  ModalityTo sys v :** Telescoped ty rhs sys v
deriving instance (SysTrav sys, Functor (ty sys), Functor (rhs sys)) => Functor (Telescoped ty rhs sys)
deriving instance (SysTrav sys, Foldable (ty sys), Foldable (rhs sys)) => Foldable (Telescoped ty rhs sys)
deriving instance (SysTrav sys, Traversable (ty sys), Traversable (rhs sys)) => Traversable (Telescoped ty rhs sys)
deriving instance (SysTrav sys, Functor (ty sys), Functor (rhs sys)) => Generic1 (Telescoped ty rhs sys)
deriving instance (SysTrav sys, NFData_ (ty sys), Functor (ty sys), NFData_ (rhs sys), Functor (rhs sys))
  => NFData_ (Telescoped ty rhs sys)
deriving instance (
    SysSyntax (Term sys) sys,
    Functor (ty sys),
    Functor (rhs sys),
    CanSwallow (Term sys) (ty sys),
    CanSwallow (Term sys) (rhs sys)
  ) => CanSwallow (Term sys) (Telescoped ty rhs sys)
infixr 3 :|-, :**

joinTelescoped :: Telescoped ty (Telescoped ty rhs) sys v -> Telescoped ty rhs sys v
joinTelescoped (Telescoped tr) = tr
joinTelescoped (seg :|- ttr) = seg :|- joinTelescoped ttr
joinTelescoped (mu :** ttr) = mu :** joinTelescoped ttr

{-| @'mapTelescopedSimple' f <theta |- rhs>@ yields @<theta |- f rhs>@ -}
mapTelescopedSimple :: (Functor h, SysTrav sys, Functor (ty sys)) =>
  (forall w . (v -> w) -> rhs1 sys w -> h (rhs2 sys w)) ->
  (Telescoped ty rhs1 sys v -> h (Telescoped ty rhs2 sys v))
mapTelescopedSimple f (Telescoped rhs) = Telescoped <$> f id rhs
mapTelescopedSimple f (seg :|- stuff) = (seg :|-) <$> mapTelescopedSimple (f . (. VarWkn)) stuff
mapTelescopedSimple f (mu :** stuff) = (mu :**) <$> mapTelescopedSimple f stuff
{-| @'mapTelescopedSimpleDB' f <theta |- rhs>@ yields @<theta |- f rhs>@ -}
mapTelescopedSimpleDB :: (Functor h, SysTrav sys, Functor (ty sys), DeBruijnLevel v) =>
  (forall w . DeBruijnLevel w => (v -> w) -> rhs1 sys w -> h (rhs2 sys w)) ->
  (Telescoped ty rhs1 sys v -> h (Telescoped ty rhs2 sys v))
mapTelescopedSimpleDB f (Telescoped rhs) = Telescoped <$> f id rhs
mapTelescopedSimpleDB f (seg :|- stuff) = (seg :|-) <$> mapTelescopedSimpleDB (f . (. VarWkn)) stuff
mapTelescopedSimpleDB f (mu :** stuff) = (mu :**) <$> mapTelescopedSimpleDB f stuff

{-
_telescoped'content :: Telescoped ty rhs sys v -> rhs sys w
_telescoped'content (Telescoped rhs) = rhs
_telescoped'content (seg :|- telescopedRHS) = _telescoped'content telescopedRHS
_telescoped'content (dmu :** telescopedRHS) = _telescoped'content telescopedRHS
-}

data ValRHS sys (v :: *) =
  ValRHS {_val'term :: Term sys v, _val'type :: Type sys v}
deriving instance (SysTrav sys) => Functor (ValRHS sys)
deriving instance (SysTrav sys) => Foldable (ValRHS sys)
deriving instance (SysTrav sys) => Traversable (ValRHS sys)
deriving instance Generic1 (ValRHS sys)
deriving instance (SysTrav sys) => NFData_ (ValRHS sys)
deriving instance (SysSyntax (Term sys) sys) =>
  CanSwallow (Term sys) (ValRHS sys)

{-
type Val = TelescopedDeclaration DeclSortVal Type ValRHS
--newtype Val (mode :: * -> *) (modty :: * -> *) (v :: *) = Val (Segment Type ValRHS sys v)
--  deriving (Functor, Foldable, Traversable, Generic1)
--deriving instance (Functor mode, Functor modty, CanSwallow (Term sys) mode, CanSwallow (Term sys) modty) =>
--  CanSwallow (Term sys) (Val sys)
_val'name :: Val sys v -> Raw.Name
_val'name seg = case _tdecl'name seg of
  DeclNameVal name -> name
-}
type Val = Declaration DeclSortVal (Telescoped Type ValRHS)
_val'name :: Val sys v -> Raw.Name
_val'name val = case _decl'name val of
  DeclNameVal name -> name

{-
data ModuleRHS (mode :: * -> *) (modty :: * -> *) (v :: *) =
  ModuleRHS {
    _module'vals :: Compose (HashMap Raw.Name) (Val sys) (VarInModule v),
    _module'modules :: Compose (HashMap String) (Module sys) (VarInModule v)
  }
  deriving (Functor, Foldable, Traversable, Generic1)
deriving instance (Functor mode, Functor modty, CanSwallow (Term sys) mode, CanSwallow (Term sys) modty) =>
  CanSwallow (Term sys) (ModuleRHS sys)
-}
{-| The entries are stored in REVERSE ORDER. -}
newtype ModuleRHS sys (v :: *) =
  ModuleRHS {_moduleRHS'content :: (Compose [] (Entry sys) (VarInModule v))}
deriving instance (SysTrav sys) => Functor (ModuleRHS sys)
deriving instance (SysTrav sys) => Foldable (ModuleRHS sys)
deriving instance (SysTrav sys) => Traversable (ModuleRHS sys)
deriving instance (SysTrav sys) => Generic1 (ModuleRHS sys)
deriving anyclass instance (SysTrav sys) => NFData_ (ModuleRHS sys)
deriving anyclass instance (SysSyntax (Term sys) sys) =>
  CanSwallow (Term sys) (ModuleRHS sys)

--type Module = TelescopedDeclaration DeclSortModule Type ModuleRHS
type Module = Declaration DeclSortModule (Telescoped Type ModuleRHS)

newModule :: ModuleRHS sys v
newModule = ModuleRHS $ Compose []
--newModule = ModuleRHS (Compose empty) (Compose empty)

addToModule :: Entry sys (VarInModule v) -> ModuleRHS sys v -> ModuleRHS sys v
addToModule entry (ModuleRHS (Compose entries)) = ModuleRHS $ Compose $ entry : entries
--addToModule (EntryVal val) = set (module'vals . _Wrapped' . at (_val'name val)) $ Just val
--addToModule (EntryModule submodule) = set (module'modules . _Wrapped' . at (_module'name submodule)) $ Just submodule

_module'name :: Module sys v -> String
_module'name modul = case _decl'name modul of
  DeclNameModule name -> name

data Entry sys (v :: *) = EntryVal (Val sys v) | EntryModule (Module sys v)
deriving instance (SysTrav sys) => Functor (Entry sys)
deriving instance (SysTrav sys) => Foldable (Entry sys)
deriving instance (SysTrav sys) => Traversable (Entry sys)
deriving instance Generic1 (Entry sys)
deriving instance (SysTrav sys) => NFData_ (Entry sys)
deriving instance (SysSyntax (Term sys) sys) =>
  CanSwallow (Term sys) (Entry sys)
withEntryDecl :: forall sys v a .
  Entry sys v ->
  (forall declSort rhs . Declaration declSort (Telescoped Type rhs) sys v -> a) ->
  a 
withEntryDecl (EntryVal val) f = f val
withEntryDecl (EntryModule modul) f = f modul
_entry'opts :: Entry sys v -> DeclOptions
_entry'opts entry = withEntryDecl entry $ _decl'opts

makeLenses ''ModuleRHS

moduleRHS'entries :: Lens' (ModuleRHS sys v) [Entry sys (VarInModule v)]
moduleRHS'entries = moduleRHS'content . _Wrapped'

------------------------------------
  
type Telescope ty = Telescoped ty Unit2

telescoped'telescope :: (SysTrav sys, Functor (ty sys)) =>
  Telescoped ty rhs sys v -> Telescope ty sys v
telescoped'telescope = runIdentity . mapTelescopedSimple (\ _ _ -> Identity Unit2)

--type LHS declSort ty = TelescopedDeclaration declSort ty Unit2
type LHS declSort ty = Declaration declSort (Telescope ty)


makeLenses ''Declaration
makeLenses ''DeclOptions
makeLenses ''LeftDivided
makeLenses ''NamedBinding
makeLenses ''ModalityTo

data UseHolesOrEliminees = UseHoles | UseEliminees
