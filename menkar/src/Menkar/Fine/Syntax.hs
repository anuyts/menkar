{- # LANGUAGE DataKinds, KindSignatures, GADTs, TypeOperators, RankNTypes #-}

module Menkar.Fine.Syntax where

import Menkar.Fine.Substitution
import GHC.Generics
import qualified Menkar.Raw.Syntax as Raw
import Data.Functor.Compose
import Data.HashMap.Lazy

{- Segment info will have to depend on v, because 'resolves' annotations have variables -}
data SegmentInfo = SegmentInfo {name :: String}
data MetaInfo where

{-
data DependentModality (mode :: * -> *) (modty :: * -> *) (v :: *) =
  NonDependentModality (ModedModality mode modty v) | Flat (mode v)
  --DependentModality {dmodDom :: mode v, dmodCod :: mode (Maybe v), dmodMod :: modty v}
  deriving (Functor, Foldable, Traversable, Generic1)
deriving instance (Functor mode, Functor modty, CanSwallow (Term mode modty) mode (Term mode modty), CanSwallow (Term mode modty) modty (Term mode modty)) =>
  CanSwallow (Term mode modty) (DependentModality mode modty) (Term mode modty)
-}

data ModedModality (mode :: * -> *) (modty :: * -> *) (v :: *) =
  ModedModality {modDom :: mode v, modMod :: modty v}
  deriving (Functor, Foldable, Traversable, Generic1)
deriving instance (Functor mode, Functor modty, CanSwallow (Term mode modty) mode, CanSwallow (Term mode modty) modty) =>
  CanSwallow (Term mode modty) (ModedModality mode modty)

data ModedContramodality (mode :: * -> *) (modty :: * -> *) (v :: *) =
  ModedContramodality {contramodDom :: mode v, contramodRightAdjoint :: modty v}
  deriving (Functor, Foldable, Traversable, Generic1)
deriving instance (Functor mode, Functor modty, CanSwallow (Term mode modty) mode, CanSwallow (Term mode modty) modty) =>
  CanSwallow (Term mode modty) (ModedContramodality mode modty)

{-
modedLeftAdjoint :: ModedModality mode modty v -> ModedContramodality mode modty v
modedLeftAdjoint (ModedModality dom cod mod) = (ModedContramodality cod dom mod)
modedRightAdjoint :: ModedContramodality mode modty v -> ModedModality mode modty v
modedRightAdjoint (ModedContramodality dom cod mod) = (ModedModality cod dom mod)
-}

------------------------------------

data Segment
     {-| Type of the types in the context. Typically @'Type'@ or @'Pair3' 'Type'@ -}
     (ty :: (* -> *) -> (* -> *) -> * -> *)
     {-| Type of the thing that lives in the context. Typically @'Type'@ or @'Pair3' 'Type'@ or some RHS-}
     (rhs :: (* -> *) -> (* -> *) -> * -> *)
     (mode :: * -> *)
     (modty :: * -> *)
     (v :: *) =
  Segment {
    segmentInfo :: SegmentInfo,
    segmentModality :: ModedModality mode modty v,
    segmentType :: Telescoped ty rhs mode modty v
  }
  deriving (Functor, Foldable, Traversable, Generic1)
deriving instance (
    Functor mode,
    Functor modty,
    Functor (ty mode modty),
    Functor (rhs mode modty),
    CanSwallow (Term mode modty) mode,
    CanSwallow (Term mode modty) modty,
    CanSwallow (Term mode modty) (ty mode modty),
    CanSwallow (Term mode modty) (rhs mode modty)
  ) => CanSwallow (Term mode modty) (Segment ty rhs mode modty)

data Binding (mode :: * -> *) (modty :: * -> *) (v :: *) =
  Binding {
    bindingSegment :: Segment Type Type mode modty v,
    bindingBody :: Term mode modty (Maybe v)
  }
  deriving (Functor, Foldable, Traversable, Generic1)
deriving instance (Functor mode, Functor modty, CanSwallow (Term mode modty) mode, CanSwallow (Term mode modty) modty) =>
  CanSwallow (Term mode modty) (Binding mode modty)

data TypeTerm (mode :: * -> *) (modty :: * -> *) (v :: *) =
  UniHS {-^ Hofmann-Streicher universe, or at least a universe that classifies its own mode. -}
    (mode v) {-^ mode (of both the universe and its elements) -}
    (Term mode modty v) {-^ level -} |
  Pi (Binding mode modty v) |
  Sigma (Binding mode modty v) |
  EmptyType |
  UnitType
  deriving (Functor, Foldable, Traversable, Generic1)
deriving instance (Functor mode, Functor modty, CanSwallow (Term mode modty) mode, CanSwallow (Term mode modty) modty) =>
  CanSwallow (Term mode modty) (TypeTerm mode modty)

data ConstructorTerm (mode :: * -> *) (modty :: * -> *) (v :: *) =
  ConsUnsafeResize
    (mode v) {-^ Type's mode -}
    (Term mode modty v) {-^ Type's proper level -}
    (Term mode modty v) {-^ Type's assigned level -}
    (TypeTerm mode modty v) {-^ Type -} |
  Lam (Binding mode modty v) |
  Pair SegmentInfo
    (ModedModality mode modty v)
    (Term mode modty v)
    (Term mode modty v) |
  ConsUnit
  deriving (Functor, Foldable, Traversable, Generic1)
deriving instance (Functor mode, Functor modty, CanSwallow (Term mode modty) mode, CanSwallow (Term mode modty) modty) =>
  CanSwallow (Term mode modty) (ConstructorTerm mode modty)

data SmartEliminator (mode :: * -> *) (modty :: * -> *) (v :: *) =
  SmartElimEnd Raw.ArgSpec |
  SmartElimArg Raw.ArgSpec (Term mode modty v) |
  SmartElimProj Raw.ProjSpec
  deriving (Functor, Foldable, Traversable, Generic1)
deriving instance (Functor mode, Functor modty, CanSwallow (Term mode modty) mode, CanSwallow (Term mode modty) modty) =>
  CanSwallow (Term mode modty) (SmartEliminator mode modty)

data Eliminator (mode :: * -> *) (modty :: * -> *) (v :: *) =
  ElimUnsafeResize
    (Term mode modty v) {-^ Type's proper level -}
    (Term mode modty v) {-^ Type's assigned level -}
    (Term mode modty v) {-^ Type -} |
  App
    (Binding mode modty v) {-^ function's pi type -} 
    (Term mode modty v) {-^ argument -} |
  ElimPair
    (Binding mode modty v) {-^ pair's sigma type -} 
    (Term mode modty (Maybe v)) {-^ motive -}
    (Term mode modty (Maybe (Maybe v))) {-^ clause -} |
  Fst
    (Binding mode modty v) {-^ pair's sigma type -} |
  Snd
    (Binding mode modty v) {-^ pair's sigma type -} |
  ElimEmpty
    (Term mode modty (Maybe v)) {-^ motive -}
  deriving (Functor, Foldable, Traversable, Generic1)
deriving instance (Functor mode, Functor modty, CanSwallow (Term mode modty) mode, CanSwallow (Term mode modty) modty) =>
  CanSwallow (Term mode modty) (Eliminator mode modty)

-- | is this useful? If not, keep it as a newtype over Term.
data Type (mode :: * -> *) (modty :: * -> *) (v :: *) =
  ElType {-^ Constructor'ish -} 
    (Term mode modty v) {-^ Type's proper level -}
    (TypeTerm mode modty v) {-^ Type -} |
  ElTerm {-^ Eliminator'ish -}
    (Term mode modty v) {-^ Type's proper level -}
    (Term mode modty v) {-^ Type -}
  deriving (Functor, Foldable, Traversable, Generic1)
deriving instance (Functor mode, Functor modty, CanSwallow (Term mode modty) mode, CanSwallow (Term mode modty) modty) =>
  CanSwallow (Term mode modty) (Type mode modty)

------------------------------------

data TermNV (mode :: * -> *) (modty :: * -> *) (v :: *) =
  TermCons (ConstructorTerm mode modty v) |
  TermElim
    (ModedModality mode modty v) {-^ modality by which the eliminee is used -}
    (Term mode modty v) {-^ eliminee -}
    (Eliminator mode modty v) {-^ eliminator -} |
  TermMeta (Compose [] (Term mode modty) v)
  deriving (Functor, Foldable, Traversable, Generic1)
deriving instance (Functor mode, Functor modty, CanSwallow (Term mode modty) mode, CanSwallow (Term mode modty) modty) =>
  CanSwallow (Term mode modty) (TermNV mode modty)

type Term mode modty = Expr (TermNV mode modty)

------------------------------------

data Telescoped
     (ty :: (* -> *) -> (* -> *) -> * -> *)
     (rhs :: (* -> *) -> (* -> *) -> * -> *)
     (mode :: * -> *)
     (modty :: * -> *)
     (v :: *) =
  Telescoped (rhs mode modty v) |
  Segment ty ty mode modty v :|- rhs mode modty (Maybe v)
  deriving (Functor, Foldable, Traversable, Generic1)
deriving instance (
    Functor mode,
    Functor modty,
    Functor (ty mode modty),
    Functor (rhs mode modty),
    CanSwallow (Term mode modty) mode,
    CanSwallow (Term mode modty) modty,
    CanSwallow (Term mode modty) (ty mode modty),
    CanSwallow (Term mode modty) (rhs mode modty)
  ) => CanSwallow (Term mode modty) (Telescoped ty rhs mode modty)

data ValRHS (mode :: * -> *) (modty :: * -> *) (v :: *) = ValRHS (Term mode modty v) (Type mode modty v)
  deriving (Functor, Foldable, Traversable, Generic1)
deriving instance (Functor mode, Functor modty, CanSwallow (Term mode modty) mode, CanSwallow (Term mode modty) modty) =>
  CanSwallow (Term mode modty) (ValRHS mode modty)

type Val = Segment Type ValRHS
--newtype Val (mode :: * -> *) (modty :: * -> *) (v :: *) = Val (Segment Type ValRHS mode modty v)
--  deriving (Functor, Foldable, Traversable, Generic1)
--deriving instance (Functor mode, Functor modty, CanSwallow (Term mode modty) mode, CanSwallow (Term mode modty) modty) =>
--  CanSwallow (Term mode modty) (Val mode modty)

data ModuleRHS (mode :: * -> *) (modty :: * -> *) (v :: *) =
  ModuleRHS {
    moduleVals :: Compose (HashMap String) (Val mode modty) v,
    moduleModules :: Compose (HashMap String) (Module mode modty) v
  }
  deriving (Functor, Foldable, Traversable, Generic1)
deriving instance (Functor mode, Functor modty, CanSwallow (Term mode modty) mode, CanSwallow (Term mode modty) modty) =>
  CanSwallow (Term mode modty) (ModuleRHS mode modty)

type Module = Segment Type ModuleRHS
--newtype Module (mode :: * -> *) (modty :: * -> *) (v :: *) = Module (Segment Type ModuleRHS mode modty v)
--  deriving (Functor, Foldable, Traversable, Generic1)
--deriving instance (Functor mode, Functor modty, CanSwallow (Term mode modty) mode, CanSwallow (Term mode modty) modty) =>
--  CanSwallow (Term mode modty) (Val mode modty)

data Entry (mode :: * -> *) (modty :: * -> *) (v :: *) = EntryVal (Val mode modty v) | EntryModule (Module mode modty v)
  deriving (Functor, Foldable, Traversable, Generic1)
deriving instance (Functor mode, Functor modty, CanSwallow (Term mode modty) mode, CanSwallow (Term mode modty) modty) =>
  CanSwallow (Term mode modty) (Entry mode modty)

------------------------------------
  
data Pair3 t (a :: ka) (b :: kb) (c :: kc) = Pair3 {fst3 :: t a b c, snd3 :: t a b c} deriving (Functor, Foldable, Traversable, Generic1)
deriving instance (CanSwallow (Term mode modty) (t mode modty)) => CanSwallow (Term mode modty) (Pair3 t mode modty)

{-
data Module (mode :: * -> *) (modty :: * -> *) (v :: *) =
  Module {
    moduleVals :: StringMap 
-}


{-
import Data.Type.Natural (Nat(..))
import Menkar.Syntax.Core

--Expression: Nothing
data SyntaxPreclass =
  PreclassMode |
  PreclassModality |
  PreclassList SyntaxClass
  --PreclassExpr2
type SyntaxClass = Maybe SyntaxPreclass
type ClassMode = Just PreclassMode
type ClassModality = Just PreclassModality
type ClassExpr = Nothing
type ClassList c = Just (PreclassList c)
--type ClassExpr2 = Just PreclassExpr2

data LamInfo where
data MetaInfo where
  
data (:##>) (arityclasses :: [(Nat, Maybe SyntaxPreclass)]) (cl :: Maybe SyntaxPreclass) :: * where
  -------------------------------------------------------
  -- | # EXPRESSIONS
  -- | domain mode, domain modality, domain, body
  Lam :: LamInfo -> '[ '(Z, ClassMode), '(Z, ClassModality), '(Z, ClassExpr), '(S Z, ClassExpr) ] :##> ClassExpr
  -- | function, argument
  App :: '[ '(Z, ClassExpr), '(Z, ClassExpr) ] :##> ClassExpr
  -- | fst mode, fst modality, fst, snd
  Pair :: '[ '(Z, ClassMode), '(Z, ClassModality), '(Z, ClassExpr), '(Z, ClassExpr) ] :##> ClassExpr
  -- | usage modality, motive, single clause
  PairElim :: '[ '(Z, ClassModality), '(S (S Z), ClassExpr), '(S (S Z), ClassExpr) ] :##> ClassExpr
  -- | any number of arguments
  Meta :: MetaInfo -> '[ '(Z, ClassList ClassExpr) ] :##> ClassExpr
  
  -------------------------------------------------------
  -- | # LISTS
  OpNil :: '[] :##> ClassList c
  OpCons :: '[ '(Z, c), '(Z, ClassList c) ] :##> ClassList c
  
  -------------------------------------------------------
  -- Expr2 :: '[ '(Z, ClassExpr), '(Z, ClassExpr) ] :##> ClassExpr2

type Expr v = Term (:##>) ClassExpr v
-}
