{- # LANGUAGE DataKinds, KindSignatures, GADTs, TypeOperators, RankNTypes, #-}
{-# LANGUAGE TemplateHaskell #-}

module Menkar.Fine.Syntax.Syntax where

import Menkar.Fine.Syntax.Substitution hiding (Expr (..))
import Menkar.Basic.Context.Variable
import GHC.Generics
import qualified Menkar.Raw.Syntax as Raw
import Data.Functor.Compose
import Data.HashMap.Lazy
import Data.Functor.Identity
import Data.Maybe
import Control.Exception.AssertFalse
import Control.Lens
import Data.Void

-------------------

data Pair3 t (a :: ka) (b :: kb) (c :: kc) = Pair3 {fst3 :: t a b c, snd3 :: t a b c}
  deriving (Functor, Foldable, Traversable, Generic1)
deriving instance (CanSwallow (Term mode modty) (t mode modty)) => CanSwallow (Term mode modty) (Pair3 t mode modty)
  
data Box3 t (a :: ka) (b :: kb) (c :: kc) = Box3 {unbox3 :: t a b c}
  deriving (Functor, Foldable, Traversable, Generic1)
deriving instance (CanSwallow (Term mode modty) (t mode modty)) => CanSwallow (Term mode modty) (Box3 t mode modty)

data Unit3 (a :: ka) (b :: kb) (c :: kc) = Unit3
  deriving (Functor, Foldable, Traversable, Generic1, Show)
deriving instance CanSwallow (Term mode modty) (Unit3 mode modty)

data Void3 (a :: ka) (b :: kb) (c :: kc) = Void3 Void
  deriving (Functor, Foldable, Traversable, Generic1)
deriving instance CanSwallow (Term mode modty) (Void3 mode modty)
absurd3 :: Void3 a b c -> d
absurd3 (Void3 v) = absurd v

data Unit1 (a :: ka) = Unit1
  deriving (Functor, Foldable, Traversable, Generic1, Show)
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
  ModedModality {modality'dom :: mode v, modality'mod :: modty v}
  deriving (Functor, Foldable, Traversable, Generic1)
deriving instance (Functor mode, Functor modty, CanSwallow (Term mode modty) mode, CanSwallow (Term mode modty) modty) =>
  CanSwallow (Term mode modty) (ModedModality mode modty)

data ModedContramodality (mode :: * -> *) (modty :: * -> *) (v :: *) =
  ModedContramodality {contramodality'dom :: mode v, contramodality'rightAdjoint :: modty v}
  deriving (Functor, Foldable, Traversable, Generic1)
deriving instance (Functor mode, Functor modty, CanSwallow (Term mode modty) mode, CanSwallow (Term mode modty) modty) =>
  CanSwallow (Term mode modty) (ModedContramodality mode modty)

newtype Mode mode modty v = Mode (mode v)
  deriving (Functor, Foldable, Traversable, Generic1)
deriving instance (CanSwallow (Term mode modty) mode) => CanSwallow (Term mode modty) (Mode mode modty)

newtype Modty mode modty v = Modty (modty v)
  deriving (Functor, Foldable, Traversable, Generic1)
deriving instance (CanSwallow (Term mode modty) modty) => CanSwallow (Term mode modty) (Modty mode modty)

data LeftDivided content mode modty v = LeftDivided {
    _leftDivided'originalMode :: mode v,
    _leftDivided'modality :: ModedModality mode modty v,
    _leftDivided'content :: content mode modty v}
  deriving (Functor, Foldable, Traversable, Generic1)
deriving instance (
    Functor mode,
    Functor modty,
    Functor (content mode modty),
    CanSwallow (Term mode modty) mode,
    CanSwallow (Term mode modty) modty,
    CanSwallow (Term mode modty) (content mode modty)
  ) => CanSwallow (Term mode modty) (LeftDivided content mode modty)

data ModApplied content mode modty v = ModApplied {
    _modApplied'modality :: ModedModality mode modty v,
    _modApplied'content :: content mode modty v}
  deriving (Functor, Foldable, Traversable, Generic1)
deriving instance (
    Functor mode,
    Functor modty,
    Functor (content mode modty),
    CanSwallow (Term mode modty) mode,
    CanSwallow (Term mode modty) modty,
    CanSwallow (Term mode modty) (content mode modty)
  ) => CanSwallow (Term mode modty) (ModApplied content mode modty)


{-
modedLeftAdjoint :: ModedModality mode modty v -> ModedContramodality mode modty v
modedLeftAdjoint (ModedModality dom cod mod) = (ModedContramodality cod dom mod)
modedRightAdjoint :: ModedContramodality mode modty v -> ModedModality mode modty v
modedRightAdjoint (ModedContramodality dom cod mod) = (ModedModality cod dom mod)
-}

------------------------------------

data Binding
    (lhs :: (* -> *) -> (* -> *) -> * -> *)
    (rhs :: (* -> *) -> (* -> *) -> * -> *)
    (mode :: * -> *) (modty :: * -> *) (v :: *) =
  Binding {
    binding'segment :: Segment lhs mode modty v,
    binding'body :: rhs mode modty (VarExt v)
  }
  deriving (Functor, Foldable, Traversable, Generic1)
deriving instance (
    Functor mode,
    Functor modty,
    Functor (lhs mode modty),
    Functor (rhs mode modty),
    CanSwallow (Term mode modty) mode,
    CanSwallow (Term mode modty) modty,
    CanSwallow (Term mode modty) (lhs mode modty),
    CanSwallow (Term mode modty) (rhs mode modty)
  ) => CanSwallow (Term mode modty) (Binding lhs rhs mode modty)
  
data NamedBinding
    (rhs :: (* -> *) -> (* -> *) -> * -> *)
    (mode :: * -> *) (modty :: * -> *) (v :: *) =
  NamedBinding {
    _namedBinding'name :: Maybe Raw.Name,
    _namedBinding'body :: rhs mode modty (VarExt v)
  }
  deriving (Functor, Foldable, Traversable, Generic1)
deriving instance (
    Functor mode,
    Functor modty,
    Functor (rhs mode modty),
    CanSwallow (Term mode modty) mode,
    CanSwallow (Term mode modty) modty,
    CanSwallow (Term mode modty) (rhs mode modty)
  ) => CanSwallow (Term mode modty) (NamedBinding rhs mode modty)

{-| HS-Types should carry no level information whatsoever:
    you couldn't type-check it, as they are definitionally irrelevant in the level.
-}
data UniHSConstructor (mode :: * -> *) (modty :: * -> *) (v :: *) =
  UniHS {-^ Hofmann-Streicher universe, or at least a universe that classifies its own mode. -}
    (mode v) {-^ mode (of both the universe and its elements) -}
    (Term mode modty v) {-^ level it classifies -} |
  Pi (Binding Type Term mode modty v) |
  Sigma (Binding Type Term mode modty v) |
  EmptyType |
  UnitType |
  BoxType (Segment Type mode modty v) |
  NatType
  deriving (Functor, Foldable, Traversable, Generic1)
deriving instance (Functor mode, Functor modty, CanSwallow (Term mode modty) mode, CanSwallow (Term mode modty) modty) =>
  CanSwallow (Term mode modty) (UniHSConstructor mode modty)

data ConstructorTerm (mode :: * -> *) (modty :: * -> *) (v :: *) =
  {-| element of the Hofmann-Streicher universe -}
  ConsUniHS
    --(mode v) {-^ Type's mode -}
    --(Term mode modty v) {-^ Type's unsafely assigned level -}
    (UniHSConstructor mode modty v) {-^ Type -} |
  Lam (Binding Type Term mode modty v) |
  Pair
    (Binding Type Term mode modty v) {-^ pair's sigma type -} 
    (Term mode modty v)
    (Term mode modty v) |
  ConsUnit |
  ConsBox
    (Segment Type mode modty v) {-^ box's type -}
    (Term mode modty v) {-^ box's content -} |
  ConsZero |
  ConsSuc (Term mode modty v)
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
  {-ElimUnsafeResize
    --(Term mode modty v) {-^ Type's unsafely assigned level -}
    {-(Term mode modty v) {-^ Type -}-} |-}
  App {
    _eliminator'argument :: (Term mode modty v)} |
  ElimSigma {
    _eliminator'motive :: (NamedBinding Term mode modty v),
    _eliminator'clausePair :: (NamedBinding (NamedBinding Term) mode modty v)} |
  Fst |
  Snd |
  ElimEmpty {
    _eliminator'motive :: (NamedBinding Term mode modty v)} |
  Unbox |
  ElimNat {
    _eliminator'motive :: (NamedBinding Term mode modty v),
    _eliminator'clauseZero :: Term mode modty v,
    _eliminator'clauseSuc :: (NamedBinding (NamedBinding Term) mode modty v)}
  deriving (Functor, Foldable, Traversable, Generic1)
deriving instance (Functor mode, Functor modty, CanSwallow (Term mode modty) mode, CanSwallow (Term mode modty) modty) =>
  CanSwallow (Term mode modty) (Eliminator mode modty)

-- | This doesn't seem particularly useful.
newtype Type (mode :: * -> *) (modty :: * -> *) (v :: *) = Type {unType :: Term mode modty v}
  {-ElType {-^ Constructor'ish -} 
    (UniHSConstructor mode modty v) {-^ Type -} |
  ElTerm {-^ Eliminator'ish -}
    (Term mode modty v) {-^ Type -}-}
  deriving (Functor, Foldable, Traversable, Generic1)
deriving instance (Functor mode, Functor modty, CanSwallow (Term mode modty) mode, CanSwallow (Term mode modty) modty) =>
  CanSwallow (Term mode modty) (Type mode modty)

------------------------------------

data TermNV (mode :: * -> *) (modty :: * -> *) (v :: *) =
  TermCons (ConstructorTerm mode modty v) |
  {-| It is an error to construct a @'TermNV'@ using @'TermElim'@ with an eliminator that
      doesn't match the SHAPE of the eliminee's type -}
  TermElim
    (ModedModality mode modty v) {-^ modality by which the eliminee is used -}
    (Term mode modty v) {-^ eliminee -}
    (Type mode modty v) {-^ eliminee's type -}
    (Eliminator mode modty v) {-^ eliminator -} |
  TermMeta Int (Compose [] (Term mode modty) v) |
  TermQName Raw.QName |
  TermSmartElim
    (Term mode modty v) {-^ eliminee -}
    (Compose [] (SmartEliminator mode modty) v) {-^ eliminators -}
    (Term mode modty v) {-^ result -} |
  TermGoal
    String {-^ goal's name -}
    (Term mode modty v) {-^ result -} |
  TermProblem {-^ Wrapper of terms that make no sense. -}
    (Term mode modty v)
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

data DeclSort = DeclSortVal | DeclSortModule | DeclSortSegment | DeclSortValSpec

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
  DeclNameValSpec :: DeclName DeclSortValSpec

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

data TelescopedPartialDeclaration
     {-| Type of the thing that lives in the context. Typically @'Type'@ or @'Pair3' 'Type'@ or some RHS-}
     (declSort :: Raw.DeclSort)
     (ty :: (* -> *) -> (* -> *) -> * -> *)
     (content :: (* -> *) -> (* -> *) -> * -> *)
     (mode :: * -> *)
     (modty :: * -> *)
     (v :: *) =
  TelescopedPartialDeclaration {
    _pdecl'names :: Maybe (Raw.DeclNames declSort),
    _pdecl'mode :: Compose Maybe mode v,
    _pdecl'modty :: Compose Maybe modty v,
    _pdecl'plicity :: Compose Maybe (Plicity mode modty) v,
    _pdecl'content :: Telescoped ty (Maybe3 content) mode modty v
    }
  deriving (Functor, Foldable, Traversable, Generic1)
deriving instance (
    Functor mode,
    Functor modty,
    Functor (ty mode modty),
    Functor (content mode modty),
    CanSwallow (Term mode modty) mode,
    CanSwallow (Term mode modty) modty,
    CanSwallow (Term mode modty) (ty mode modty),
    CanSwallow (Term mode modty) (content mode modty)
  ) => CanSwallow (Term mode modty) (TelescopedPartialDeclaration declSort ty content mode modty)
  
newPartialDeclaration :: TelescopedPartialDeclaration declSort ty content mode modty v
newPartialDeclaration = TelescopedPartialDeclaration {
  _pdecl'names = Nothing,
  _pdecl'mode = Compose Nothing,
  _pdecl'modty = Compose Nothing,
  _pdecl'plicity = Compose Nothing,
  _pdecl'content = Telescoped $ Maybe3 $ Compose $ Nothing
  }

--type TelescopedDeclaration declSort ty content = Telescoped ty (Declaration declSort content)
type Segment ty = Declaration DeclSortSegment ty

--type TelescopedPartialDeclaration declSort ty content = Telescoped ty (PartialDeclaration declSort content)
type PartialSegment ty = TelescopedPartialDeclaration Raw.DeclSortSegment Void3 ty

{-
_tdecl'name :: TelescopedDeclaration declSort ty content mode modty v -> DeclName declSort
_tdecl'name (Telescoped decl) = _decl'name decl
_tdecl'name (seg :|- tdecl) = _tdecl'name tdecl
_tdecl'name (mu :** tdecl) = _tdecl'name tdecl -}
_segment'name :: Segment ty mode modty v -> Maybe Raw.Name
_segment'name seg = case _decl'name seg of
  DeclNameSegment maybeName -> maybeName
_segment'content = _decl'content
_segment'modty = _decl'modty

data Telescoped
     (ty :: (* -> *) -> (* -> *) -> * -> *)
     (rhs :: (* -> *) -> (* -> *) -> * -> *)
     (mode :: * -> *)
     (modty :: * -> *)
     (v :: *) =
  Telescoped (rhs mode modty v) |
  Segment ty mode modty v :|- Telescoped ty rhs mode modty (VarExt v) |
  ModedModality mode modty v :** Telescoped ty rhs mode modty v
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

joinTelescoped :: Telescoped ty (Telescoped ty rhs) mode modty v -> Telescoped ty rhs mode modty v
joinTelescoped (Telescoped tr) = tr
joinTelescoped (seg :|- ttr) = seg :|- joinTelescoped ttr
joinTelescoped (mu :** ttr) = mu :** joinTelescoped ttr

{-| @'mapTelescopedSimple' f <theta |- rhs>@ yields @<theta |- f rhs>@ -}
mapTelescopedSimple :: (Functor h, Functor mode, Functor modty, Functor (ty mode modty)) =>
  (forall w . (v -> w) -> rhs1 mode modty w -> h (rhs2 mode modty w)) ->
  (Telescoped ty rhs1 mode modty v -> h (Telescoped ty rhs2 mode modty v))
mapTelescopedSimple f (Telescoped rhs) = Telescoped <$> f id rhs
mapTelescopedSimple f (seg :|- stuff) = (seg :|-) <$> mapTelescopedSimple (f . (. VarWkn)) stuff
mapTelescopedSimple f (mu :** stuff) = (mu :**) <$> mapTelescopedSimple f stuff

makeLenses ''Declaration
makeLenses ''TelescopedPartialDeclaration

data ValRHS (mode :: * -> *) (modty :: * -> *) (v :: *) =
  ValRHS {_val'term :: Term mode modty v, _val'type :: Type mode modty v}
  deriving (Functor, Foldable, Traversable, Generic1)
deriving instance (Functor mode, Functor modty, CanSwallow (Term mode modty) mode, CanSwallow (Term mode modty) modty) =>
  CanSwallow (Term mode modty) (ValRHS mode modty)

{-
type Val = TelescopedDeclaration DeclSortVal Type ValRHS
--newtype Val (mode :: * -> *) (modty :: * -> *) (v :: *) = Val (Segment Type ValRHS mode modty v)
--  deriving (Functor, Foldable, Traversable, Generic1)
--deriving instance (Functor mode, Functor modty, CanSwallow (Term mode modty) mode, CanSwallow (Term mode modty) modty) =>
--  CanSwallow (Term mode modty) (Val mode modty)
_val'name :: Val mode modty v -> Raw.Name
_val'name seg = case _tdecl'name seg of
  DeclNameVal name -> name
-}
type Val = Declaration DeclSortVal (Telescoped Type ValRHS)
_val'name :: Val mode modty v -> Raw.Name
_val'name val = case _decl'name val of
  DeclNameVal name -> name

{-
data ModuleRHS (mode :: * -> *) (modty :: * -> *) (v :: *) =
  ModuleRHS {
    _module'vals :: Compose (HashMap Raw.Name) (Val mode modty) (VarInModule v),
    _module'modules :: Compose (HashMap String) (Module mode modty) (VarInModule v)
  }
  deriving (Functor, Foldable, Traversable, Generic1)
deriving instance (Functor mode, Functor modty, CanSwallow (Term mode modty) mode, CanSwallow (Term mode modty) modty) =>
  CanSwallow (Term mode modty) (ModuleRHS mode modty)
-}
{-| The entries are stored in REVERSE ORDER. -}
newtype ModuleRHS (mode :: * -> *) (modty :: * -> *) (v :: *) =
  ModuleRHS {_moduleRHS'content :: (Compose [] (Entry mode modty) (VarInModule v))}
  deriving (Functor, Foldable, Traversable, Generic1)
deriving instance (Functor mode, Functor modty, CanSwallow (Term mode modty) mode, CanSwallow (Term mode modty) modty) =>
  CanSwallow (Term mode modty) (ModuleRHS mode modty)

--type Module = TelescopedDeclaration DeclSortModule Type ModuleRHS
type Module = Declaration DeclSortModule (Telescoped Type ModuleRHS)

newModule :: ModuleRHS mode modty v
newModule = ModuleRHS $ Compose []
--newModule = ModuleRHS (Compose empty) (Compose empty)

addToModule :: Entry mode modty (VarInModule v) -> ModuleRHS mode modty v -> ModuleRHS mode modty v
addToModule entry (ModuleRHS (Compose entries)) = ModuleRHS $ Compose $ entry : entries
--addToModule (EntryVal val) = set (module'vals . _Wrapped' . at (_val'name val)) $ Just val
--addToModule (EntryModule submodule) = set (module'modules . _Wrapped' . at (_module'name submodule)) $ Just submodule

_module'name :: Module mode modty v -> String
_module'name modul = case _decl'name modul of
  DeclNameModule name -> name

data Entry (mode :: * -> *) (modty :: * -> *) (v :: *) = EntryVal (Val mode modty v) | EntryModule (Module mode modty v)
  deriving (Functor, Foldable, Traversable, Generic1)
deriving instance (Functor mode, Functor modty, CanSwallow (Term mode modty) mode, CanSwallow (Term mode modty) modty) =>
  CanSwallow (Term mode modty) (Entry mode modty)

makeLenses ''ModuleRHS

moduleRHS'entries :: Lens' (ModuleRHS mode modty v) [Entry mode modty (VarInModule v)]
moduleRHS'entries = moduleRHS'content . _Wrapped'

------------------------------------
  
type Telescope ty = Telescoped ty Unit3

telescoped'telescope :: (Functor mode, Functor modty, Functor (ty mode modty)) =>
  Telescoped ty rhs mode modty v -> Telescope ty mode modty v
telescoped'telescope = runIdentity . mapTelescopedSimple (\ _ _ -> Identity Unit3)

--type LHS declSort ty = TelescopedDeclaration declSort ty Unit3
type LHS declSort ty = Declaration declSort (Telescope ty)

makeLenses ''LeftDivided
makeLenses ''NamedBinding
