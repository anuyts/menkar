{- # LANGUAGE DataKinds, KindSignatures, GADTs, TypeOperators, RankNTypes, #-}
{-# LANGUAGE TemplateHaskell #-}

module Menkar.Fine.Syntax where

import Menkar.Fine.Substitution
import Menkar.Fine.Context.Variable
import GHC.Generics
import qualified Menkar.Raw.Syntax as Raw
import Data.Functor.Compose
import Data.HashMap.Lazy
import Data.Functor.Identity
import Data.Maybe
import Control.Exception.AssertFalse
import Control.Lens

{- Segment info will have to depend on v, because 'resolves' annotations have variables -}
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

data Binding (mode :: * -> *) (modty :: * -> *) (v :: *) =
  Binding {
    bindingSegment :: Segment Type mode modty v,
    bindingBody :: Term mode modty (VarExt v)
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
  Pair
    (Binding mode modty v) {-^ pair's sigma type -} 
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
  TermMeta (Compose [] (Term mode modty) v) |
  TermSmartElim
    (Term mode modty v) {-^ eliminate -}
    (Compose [] (SmartEliminator mode modty) v) {-^ eliminators -}
    (Term mode modty v) {-^ result -}
  deriving (Functor, Foldable, Traversable, Generic1)
deriving instance (Functor mode, Functor modty, CanSwallow (Term mode modty) mode, CanSwallow (Term mode modty) modty) =>
  CanSwallow (Term mode modty) (TermNV mode modty)

type Term mode modty = Expr (TermNV mode modty)

------------------------------------

--data SegmentInfo = SegmentInfo {name :: String}

data Annotation mode modty v =
  AnnotMode (mode v) |
  AnnotModality (modty v) |
  AnnotImplicit
  --AnnotResolves (Term )
  deriving (Functor, Foldable, Traversable, Generic1)
deriving instance (Functor mode, Functor modty, CanSwallow (Term mode modty) mode, CanSwallow (Term mode modty) modty) =>
  CanSwallow (Term mode modty) (Annotation mode modty)

data Plicity mode modty v =
  Explicit |
  Implicit |
  Resolves (Term mode modty v) -- this may change
  deriving (Functor, Foldable, Traversable, Generic1)
deriving instance (Functor mode, Functor modty, CanSwallow (Term mode modty) mode, CanSwallow (Term mode modty) modty) =>
  CanSwallow (Term mode modty) (Plicity mode modty)

data Declaration
     {-| Type of the thing that lives in the context. Typically @'Type'@ or @'Pair3' 'Type'@ or some RHS-}
     (content :: (* -> *) -> (* -> *) -> * -> *)
     (mode :: * -> *)
     (modty :: * -> *)
     (v :: *) =
  Declaration {
    decl'name :: Maybe Raw.Name,
    decl'modty :: ModedModality mode modty v,
    decl'plicity :: Plicity mode modty v,
    decl'content :: content mode modty v
  }
  deriving (Functor, Foldable, Traversable, Generic1)
deriving instance (
    Functor mode,
    Functor modty,
    Functor (content mode modty),
    CanSwallow (Term mode modty) mode,
    CanSwallow (Term mode modty) modty,
    CanSwallow (Term mode modty) (content mode modty)
  ) => CanSwallow (Term mode modty) (Declaration content mode modty)

data PartialDeclaration
     {-| Type of the thing that lives in the context. Typically @'Type'@ or @'Pair3' 'Type'@ or some RHS-}
     (content :: (* -> *) -> (* -> *) -> * -> *)
     (mode :: * -> *)
     (modty :: * -> *)
     (v :: *) =
  PartialDeclaration {
    _pdecl'names :: Raw.LHSNames,
    _pdecl'mode :: Compose Maybe mode v,
    _pdecl'modty :: Compose Maybe modty v,
    _pdecl'plicity :: Compose Maybe (Plicity mode modty) v,
    _pdecl'content :: Compose Maybe (content mode modty) v
    }
  deriving (Functor, Foldable, Traversable, Generic1)
deriving instance (
    Functor mode,
    Functor modty,
    Functor (content mode modty),
    CanSwallow (Term mode modty) mode,
    CanSwallow (Term mode modty) modty,
    CanSwallow (Term mode modty) (content mode modty)
  ) => CanSwallow (Term mode modty) (PartialDeclaration content mode modty)
  
newPartialDeclaration :: PartialDeclaration content mode modty v
newPartialDeclaration = PartialDeclaration {
  _pdecl'names = Raw.SomeNamesForTelescope [],
  _pdecl'mode = Compose Nothing,
  _pdecl'modty = Compose Nothing,
  _pdecl'plicity = Compose Nothing,
  _pdecl'content = Compose Nothing
  }

type TelescopedDeclaration ty content = Telescoped ty (Declaration content)
type Segment ty = TelescopedDeclaration ty ty

type TelescopedPartialDeclaration ty content = Telescoped ty (PartialDeclaration content)
type PartialSegment ty = TelescopedPartialDeclaration ty ty

tdecl'name :: TelescopedDeclaration ty content mode modty v -> Maybe Raw.Name
tdecl'name (Telescoped decl) = decl'name decl
tdecl'name (seg :|- tdecl) = tdecl'name tdecl
segment'name :: Segment ty mode modty v -> Maybe Raw.Name
segment'name = tdecl'name

data Telescoped
     (ty :: (* -> *) -> (* -> *) -> * -> *)
     (rhs :: (* -> *) -> (* -> *) -> * -> *)
     (mode :: * -> *)
     (modty :: * -> *)
     (v :: *) =
  Telescoped (rhs mode modty v) |
  TelescopedDeclaration ty ty mode modty v :|- Telescoped ty rhs mode modty (VarExt v)
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

makeLenses ''PartialDeclaration

{-
data Segment
     {-| Type of the types in the context. Typically @'Type'@ or @'Pair3' 'Type'@ -}
     (ty :: (* -> *) -> (* -> *) -> * -> *)
     {-| Type of the thing that lives in the context. Typically @'Type'@ or @'Pair3' 'Type'@ or some RHS-}
     (rhs :: (* -> *) -> (* -> *) -> * -> *)
     (mode :: * -> *)
     (modty :: * -> *)
     (v :: *) =
  Segment {
    --segmentInfo :: SegmentInfo,
    --segmentAnnots :: Compose [] (Annotation mode modty) v,
    segmentName :: Maybe Raw.Name,
    segmentModality :: ModedModality mode modty v,
    segmentPlicity :: Plicity mode modty v,
    segmentRHS :: Telescoped ty rhs mode modty v,
    segmentRightCartesian :: Bool -- This is useless, it follows from the use of :^^
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

data SegmentBuilder
     {-| Type of the types in the context. Typically @'Type'@ or @'Pair3' 'Type'@ -}
     (ty :: (* -> *) -> (* -> *) -> * -> *)
     {-| Type of the thing that lives in the context. Typically @'Type'@ or @'Pair3' 'Type'@ or some RHS-}
     (rhs :: (* -> *) -> (* -> *) -> * -> *)
     (mode :: * -> *)
     (modty :: * -> *)
     (v :: *) =
  SegmentBuilder {
    segmentBuilderNames :: Raw.LHSNames,
    segmentBuilderMode :: Compose Maybe mode v,
    segmentBuilderModality :: Compose Maybe modty v,
    segmentBuilderPlicity :: Compose Maybe (Plicity mode modty) v,
    segmentBuilderTelescopedType :: (Telescoped ty (Maybe3 rhs) mode modty) v
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
  ) => CanSwallow (Term mode modty) (SegmentBuilder ty rhs mode modty)
newSegmentBuilder :: SegmentBuilder ty rhs mode modty v
newSegmentBuilder = SegmentBuilder {
    segmentBuilderNames = Raw.SomeNamesForTelescope [],
    segmentBuilderMode = (Compose Nothing),
    segmentBuilderModality = (Compose Nothing),
    segmentBuilderPlicity = (Compose Nothing),
    segmentBuilderTelescopedType = (Telescoped . Maybe3 . Compose $ Nothing)
  }

data Telescoped
     (ty :: (* -> *) -> (* -> *) -> * -> *)
     (rhs :: (* -> *) -> (* -> *) -> * -> *)
     (mode :: * -> *)
     (modty :: * -> *)
     (v :: *) =
  Telescoped (rhs mode modty v) |
  Segment ty ty mode modty v :|- Telescoped ty rhs mode modty (VarExt v)
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
-}

data ValRHS (mode :: * -> *) (modty :: * -> *) (v :: *) = ValRHS (Term mode modty v) (Type mode modty v)
  deriving (Functor, Foldable, Traversable, Generic1)
deriving instance (Functor mode, Functor modty, CanSwallow (Term mode modty) mode, CanSwallow (Term mode modty) modty) =>
  CanSwallow (Term mode modty) (ValRHS mode modty)

type Val = TelescopedDeclaration Type ValRHS
--newtype Val (mode :: * -> *) (modty :: * -> *) (v :: *) = Val (Segment Type ValRHS mode modty v)
--  deriving (Functor, Foldable, Traversable, Generic1)
--deriving instance (Functor mode, Functor modty, CanSwallow (Term mode modty) mode, CanSwallow (Term mode modty) modty) =>
--  CanSwallow (Term mode modty) (Val mode modty)

data ModuleRHS (mode :: * -> *) (modty :: * -> *) (v :: *) =
  ModuleRHS {
    moduleVals :: Compose (HashMap Raw.Name) (Val mode modty) (VarInModule v),
    moduleModules :: Compose (HashMap String) (Module mode modty) (VarInModule v)
  }
  deriving (Functor, Foldable, Traversable, Generic1)
deriving instance (Functor mode, Functor modty, CanSwallow (Term mode modty) mode, CanSwallow (Term mode modty) modty) =>
  CanSwallow (Term mode modty) (ModuleRHS mode modty)
newModule :: ModuleRHS mode modty v
newModule = ModuleRHS (Compose empty) (Compose empty)
addToModule :: ModuleRHS mode modty v -> Entry mode modty (VarInModule v) -> ModuleRHS mode modty v
addToModule modul (EntryVal val) =
  modul {moduleVals = Compose $
          update (const $ Just val) (fromMaybe (assertFalse "nameless val") $ tdecl'name val) $
          getCompose $ moduleVals modul
        }
addToModule modul (EntryModule submodule) =
  modul {moduleModules = Compose $
          update (const $ Just submodule) (Raw.stringName $ fromMaybe (assertFalse "nameless val") $ tdecl'name submodule) $
          getCompose $ moduleModules modul
        }

type Module = TelescopedDeclaration Type ModuleRHS
--newtype Module (mode :: * -> *) (modty :: * -> *) (v :: *) = Module (Segment Type ModuleRHS mode modty v)
--  deriving (Functor, Foldable, Traversable, Generic1)
--deriving instance (Functor mode, Functor modty, CanSwallow (Term mode modty) mode, CanSwallow (Term mode modty) modty) =>
--  CanSwallow (Term mode modty) (Val mode modty)

data Entry (mode :: * -> *) (modty :: * -> *) (v :: *) = EntryVal (Val mode modty v) | EntryModule (Module mode modty v)
  deriving (Functor, Foldable, Traversable, Generic1)
deriving instance (Functor mode, Functor modty, CanSwallow (Term mode modty) mode, CanSwallow (Term mode modty) modty) =>
  CanSwallow (Term mode modty) (Entry mode modty)

------------------------------------
  
data Pair3 t (a :: ka) (b :: kb) (c :: kc) = Pair3 {fst3 :: t a b c, snd3 :: t a b c}
  deriving (Functor, Foldable, Traversable, Generic1)
deriving instance (CanSwallow (Term mode modty) (t mode modty)) => CanSwallow (Term mode modty) (Pair3 t mode modty)

data Unit3 (a :: ka) (b :: kb) (c :: kc) = Unit3
  deriving (Functor, Foldable, Traversable, Generic1)
deriving instance CanSwallow (Term mode modty) (Unit3 mode modty)

data Unit1 (a :: ka) = Unit1
  deriving (Functor, Foldable, Traversable, Generic1)
deriving instance CanSwallow (Term mode modty) (Unit1)

newtype Maybe3 t (a :: ka) (b :: kb) (c :: kc) = Maybe3 (Compose Maybe (t a b) c)
  deriving (Functor, Foldable, Traversable, Generic1)
deriving instance (
    CanSwallow (Term mode modty) mode,
    CanSwallow (Term mode modty) modty,
    CanSwallow (Term mode modty) (t mode modty)
  ) =>
  CanSwallow (Term mode modty) (Maybe3 t mode modty)

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
