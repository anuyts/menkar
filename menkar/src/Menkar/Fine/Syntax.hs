{- # LANGUAGE DataKinds, KindSignatures, GADTs, TypeOperators, RankNTypes, #-}
{-# LANGUAGE TemplateHaskell #-}

module Menkar.Fine.Syntax where

import Menkar.Fine.Substitution hiding (Expr (..))
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
--data MetaInfo where

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

newtype Mode mode modty v = Mode (mode v)
  deriving (Functor, Foldable, Traversable, Generic1)
deriving instance (CanSwallow (Term mode modty) mode) => CanSwallow (Term mode modty) (Mode mode modty)

newtype Modty mode modty v = Modty (modty v)
  deriving (Functor, Foldable, Traversable, Generic1)
deriving instance (CanSwallow (Term mode modty) modty) => CanSwallow (Term mode modty) (Modty mode modty)


{-
modedLeftAdjoint :: ModedModality mode modty v -> ModedContramodality mode modty v
modedLeftAdjoint (ModedModality dom cod mod) = (ModedContramodality cod dom mod)
modedRightAdjoint :: ModedContramodality mode modty v -> ModedModality mode modty v
modedRightAdjoint (ModedContramodality dom cod mod) = (ModedModality cod dom mod)
-}

------------------------------------

data Binding (rhs :: (* -> *) -> (* -> *) -> * -> *) (mode :: * -> *) (modty :: * -> *) (v :: *) =
  Binding {
    binding'segment :: Segment Type mode modty v,
    binding'body :: rhs mode modty (VarExt v)
  }
  deriving (Functor, Foldable, Traversable, Generic1)
deriving instance (
    Functor mode,
    Functor modty,
    Functor (rhs mode modty),
    CanSwallow (Term mode modty) mode,
    CanSwallow (Term mode modty) modty,
    CanSwallow (Term mode modty) (rhs mode modty)
  ) => CanSwallow (Term mode modty) (Binding rhs mode modty)

{-| HS-Types should carry no level information whatsoever:
    you couldn't type-check it, as they are definitionally irrelevant in the level.
-}
data TypeTerm (mode :: * -> *) (modty :: * -> *) (v :: *) =
  UniHS {-^ Hofmann-Streicher universe, or at least a universe that classifies its own mode. -}
    (mode v) {-^ mode (of both the universe and its elements) -}
    (Term mode modty v) {-^ level it classifies -} |
  Pi (Binding Term mode modty v) |
  Sigma (Binding Term mode modty v) |
  EmptyType |
  UnitType
  deriving (Functor, Foldable, Traversable, Generic1)
deriving instance (Functor mode, Functor modty, CanSwallow (Term mode modty) mode, CanSwallow (Term mode modty) modty) =>
  CanSwallow (Term mode modty) (TypeTerm mode modty)

data ConstructorTerm (mode :: * -> *) (modty :: * -> *) (v :: *) =
  {-| element of the Hofmann-Streicher universe -}
  ConsUniHS
    (mode v) {-^ Type's mode -}
    --(Term mode modty v) {-^ Type's unsafely assigned level -}
    (TypeTerm mode modty v) {-^ Type -} |
  Lam (Binding Term mode modty v) |
  Pair
    (Binding Term mode modty v) {-^ pair's sigma type -} 
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
    --(Term mode modty v) {-^ Type's unsafely assigned level -}
    {-(Term mode modty v) {-^ Type -}-} |
  App
    (Binding Term mode modty v) {-^ function's pi type -} 
    (Term mode modty v) {-^ argument -} |
  ElimPair
    --(Binding Term mode modty v) {-^ pair's sigma type -} 
    (Binding Term mode modty v) {-^ motive -}
    (Binding (Binding Term) mode modty v) {-^ clause -} |
  Fst
    (Binding Term mode modty v) {-^ pair's sigma type -} |
  Snd
    (Binding Term mode modty v) {-^ pair's sigma type -} |
  ElimEmpty
    (Binding Term mode modty v) {-^ motive -}
  deriving (Functor, Foldable, Traversable, Generic1)
deriving instance (Functor mode, Functor modty, CanSwallow (Term mode modty) mode, CanSwallow (Term mode modty) modty) =>
  CanSwallow (Term mode modty) (Eliminator mode modty)

-- | This doesn't seem particularly useful.
newtype Type (mode :: * -> *) (modty :: * -> *) (v :: *) = Type (Term mode modty v)
  {-ElType {-^ Constructor'ish -} 
    (TypeTerm mode modty v) {-^ Type -} |
  ElTerm {-^ Eliminator'ish -}
    (Term mode modty v) {-^ Type -}-}
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
  TermMeta Int (Compose [] (Term mode modty) v)
  {-- |
  TermSmartElim
    (Term mode modty v) {-^ eliminate -}
    (Compose [] (SmartEliminator mode modty) v) {-^ eliminators -}
    (Term mode modty v) {-^ result -} -}
  deriving (Functor, Foldable, Traversable, Generic1)
deriving instance (Functor mode, Functor modty, CanSwallow (Term mode modty) mode, CanSwallow (Term mode modty) modty) =>
  CanSwallow (Term mode modty) (TermNV mode modty)

type Term = Expr3 TermNV

------------------------------------

--data SegmentInfo = SegmentInfo {name :: String}

{-| Not used in segments. Used by the scoper, and also used for annotation entries. -}
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

data DeclSort = DeclSortVal | DeclSortModule | DeclSortSegment

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

{-
data DeclType
     (declSort :: DeclSort)
     (mode :: * -> *)
     (modty :: * -> *)
     (v :: *) where
  DeclTypeVal :: Type mode modty v -> DeclType DeclSortVal mode modty v
  DeclTypeModule :: DeclType DeclSortModule mode modty v
  DeclTypeSegment :: (a -> Type mode modty v) -> DeclType (DeclSortSegment a) mode modty v  
-}

data Declaration
     {-| Type of the thing that lives in the context. Typically @'Type'@ or @'Pair3' 'Type'@ or some RHS-}
     (declSort :: DeclSort)
     (content :: (* -> *) -> (* -> *) -> * -> *)
     (mode :: * -> *)
     (modty :: * -> *)
     (v :: *) =
  Declaration {
    _decl'name :: DeclName declSort,
    _decl'modty :: ModedModality mode modty v,
    _decl'plicity :: Plicity mode modty v,
    _decl'content :: content mode modty v
  }
  deriving (Functor, Foldable, Traversable, Generic1)
deriving instance (
    Functor mode,
    Functor modty,
    Functor (content mode modty),
    CanSwallow (Term mode modty) mode,
    CanSwallow (Term mode modty) modty,
    CanSwallow (Term mode modty) (content mode modty)
  ) => CanSwallow (Term mode modty) (Declaration declSort content mode modty)

data PartialDeclaration
     {-| Type of the thing that lives in the context. Typically @'Type'@ or @'Pair3' 'Type'@ or some RHS-}
     (declSort :: Raw.DeclSort)
     (content :: (* -> *) -> (* -> *) -> * -> *)
     (mode :: * -> *)
     (modty :: * -> *)
     (v :: *) =
  PartialDeclaration {
    _pdecl'names :: Maybe (Raw.DeclNames declSort),
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
  ) => CanSwallow (Term mode modty) (PartialDeclaration declSort content mode modty)
  
newPartialDeclaration :: PartialDeclaration declSort content mode modty v
newPartialDeclaration = PartialDeclaration {
  _pdecl'names = Nothing,
  _pdecl'mode = Compose Nothing,
  _pdecl'modty = Compose Nothing,
  _pdecl'plicity = Compose Nothing,
  _pdecl'content = Compose Nothing
  }

type TelescopedDeclaration declSort ty content = Telescoped ty (Declaration declSort content)
type Segment ty = TelescopedDeclaration DeclSortSegment ty ty

type TelescopedPartialDeclaration declSort ty content = Telescoped ty (PartialDeclaration declSort content)
type PartialSegment ty = TelescopedPartialDeclaration Raw.DeclSortSegment ty ty

_tdecl'name :: TelescopedDeclaration declSort ty content mode modty v -> DeclName declSort
_tdecl'name (Telescoped decl) = _decl'name decl
_tdecl'name (seg :|- tdecl) = _tdecl'name tdecl
_segment'name :: Segment ty mode modty v -> Maybe Raw.Name
_segment'name seg = case _tdecl'name seg of
  DeclNameSegment maybeName -> maybeName

data Telescoped
     (ty :: (* -> *) -> (* -> *) -> * -> *)
     (rhs :: (* -> *) -> (* -> *) -> * -> *)
     (mode :: * -> *)
     (modty :: * -> *)
     (v :: *) =
  Telescoped (rhs mode modty v) |
  Segment ty mode modty v :|- Telescoped ty rhs mode modty (VarExt v)
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

{-| @'mapTelescopedSimple' f <theta |- rhs>@ yields @<theta |- f rhs>@ -}
mapTelescopedSimple :: (Functor h, Functor mode, Functor modty, Functor (ty mode modty)) =>
  (forall w . (v -> w) -> rhs1 mode modty w -> h (rhs2 mode modty w)) ->
  (Telescoped ty rhs1 mode modty v -> h (Telescoped ty rhs2 mode modty v))
mapTelescopedSimple f (Telescoped rhs) = Telescoped <$> f id rhs
mapTelescopedSimple f (seg :|- stuff) = (seg :|-) <$> mapTelescopedSimple (f . (. VarWkn)) stuff

makeLenses ''Declaration
makeLenses ''PartialDeclaration

data ValRHS (mode :: * -> *) (modty :: * -> *) (v :: *) = ValRHS (Term mode modty v) (Type mode modty v)
  deriving (Functor, Foldable, Traversable, Generic1)
deriving instance (Functor mode, Functor modty, CanSwallow (Term mode modty) mode, CanSwallow (Term mode modty) modty) =>
  CanSwallow (Term mode modty) (ValRHS mode modty)

type Val = TelescopedDeclaration DeclSortVal Type ValRHS
--newtype Val (mode :: * -> *) (modty :: * -> *) (v :: *) = Val (Segment Type ValRHS mode modty v)
--  deriving (Functor, Foldable, Traversable, Generic1)
--deriving instance (Functor mode, Functor modty, CanSwallow (Term mode modty) mode, CanSwallow (Term mode modty) modty) =>
--  CanSwallow (Term mode modty) (Val mode modty)
_val'name :: Val mode modty v -> Raw.Name
_val'name seg = case _tdecl'name seg of
  DeclNameVal name -> name

data ModuleRHS (mode :: * -> *) (modty :: * -> *) (v :: *) =
  ModuleRHS {
    _module'vals :: Compose (HashMap Raw.Name) (Val mode modty) (VarInModule v),
    _module'modules :: Compose (HashMap String) (Module mode modty) (VarInModule v)
  }
  deriving (Functor, Foldable, Traversable, Generic1)
deriving instance (Functor mode, Functor modty, CanSwallow (Term mode modty) mode, CanSwallow (Term mode modty) modty) =>
  CanSwallow (Term mode modty) (ModuleRHS mode modty)

type Module = TelescopedDeclaration DeclSortModule Type ModuleRHS

makeLenses ''ModuleRHS

newModule :: ModuleRHS mode modty v
newModule = ModuleRHS (Compose empty) (Compose empty)
addToModule :: Entry mode modty (VarInModule v) -> ModuleRHS mode modty v -> ModuleRHS mode modty v
addToModule (EntryVal val) = set (module'vals . _Wrapped' . at (_val'name val)) $ Just val
addToModule (EntryModule submodule) = set (module'modules . _Wrapped' . at (_module'name submodule)) $ Just submodule

_module'name :: Module mode modty v -> String
_module'name seg = case _tdecl'name seg of
  DeclNameModule name -> name

data Entry (mode :: * -> *) (modty :: * -> *) (v :: *) = EntryVal (Val mode modty v) | EntryModule (Module mode modty v)
  deriving (Functor, Foldable, Traversable, Generic1)
deriving instance (Functor mode, Functor modty, CanSwallow (Term mode modty) mode, CanSwallow (Term mode modty) modty) =>
  CanSwallow (Term mode modty) (Entry mode modty)

------------------------------------
  
data Pair3 t (a :: ka) (b :: kb) (c :: kc) = Pair3 {fst3 :: t a b c, snd3 :: t a b c}
  deriving (Functor, Foldable, Traversable, Generic1)
deriving instance (CanSwallow (Term mode modty) (t mode modty)) => CanSwallow (Term mode modty) (Pair3 t mode modty)
  
data Box3 t (a :: ka) (b :: kb) (c :: kc) = Box3 {unbox3 :: t a b c}
  deriving (Functor, Foldable, Traversable, Generic1)
deriving instance (CanSwallow (Term mode modty) (t mode modty)) => CanSwallow (Term mode modty) (Box3 t mode modty)

data Unit3 (a :: ka) (b :: kb) (c :: kc) = Unit3
  deriving (Functor, Foldable, Traversable, Generic1)
deriving instance CanSwallow (Term mode modty) (Unit3 mode modty)

data Void3 (a :: ka) (b :: kb) (c :: kc) where
  deriving (Functor, Foldable, Traversable, Generic1)
deriving instance CanSwallow (Term mode modty) (Void3 mode modty)

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

-------------------

type Telescope ty = Telescoped ty Unit3

telescoped'telescope :: (Functor mode, Functor modty, Functor (ty mode modty)) =>
  Telescoped ty rhs mode modty v -> Telescope ty mode modty v
telescoped'telescope = runIdentity . mapTelescopedSimple (\ _ _ -> Identity Unit3)

type LHS declSort ty = TelescopedDeclaration declSort ty Unit3
