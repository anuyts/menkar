{- # LANGUAGE DataKinds, KindSignatures, GADTs, TypeOperators, RankNTypes #-}

module Menkar.Syntax.Syntax where

import Menkar.Syntax.Composable
import GHC.Generics
import qualified Menkar.Raw.Base as Raw
import Data.Functor.Compose

data SegmentInfo = SegmentInfo {name :: String}
data MetaInfo where

data ModedModality (mode :: * -> *) (mhom :: * -> *) (v :: *) =
  ModedModality {domMode :: mode v, codMode :: mode v, modality :: mhom v}
  deriving (Functor, Foldable, Traversable, Generic1)
deriving instance (Functor mode, Functor mhom, Swallows mode (Term mode mhom), Swallows mhom (Term mode mhom)) =>
  Swallows (ModedModality mode mhom) (Term mode mhom)

data Segment (t :: (* -> *) -> (* -> *) -> * -> *) (mode :: * -> *) (mhom :: * -> *) (v :: *) =
  Segment {
    segmentInfo :: SegmentInfo,
    segmentModality :: ModedModality mode mhom v,
    segmentType :: t mode mhom v
  }
  deriving (Functor, Foldable, Traversable, Generic1)
deriving instance (
    Functor mode,
    Functor mhom,
    Swallows mode (Term mode mhom),
    Swallows mhom (Term mode mhom),
    Swallows (t mode mhom) (Term mode mhom)
  ) => Swallows (Segment t mode mhom) (Term mode mhom)

data Binding (mode :: * -> *) (mhom :: * -> *) (v :: *) =
  Binding {
    bindingSegment :: Segment Type mode mhom v,
    bindingBody :: Term mode mhom (Maybe v)
  }
  deriving (Functor, Foldable, Traversable, Generic1)
deriving instance (Functor mode, Functor mhom, Swallows mode (Term mode mhom), Swallows mhom (Term mode mhom)) =>
  Swallows (Binding mode mhom) (Term mode mhom)

data TypeTerm (mode :: * -> *) (mhom :: * -> *) (v :: *) =
  UniHS {-^ Hofmann-Streicher universe, or at least a universe that classifies its own mode. -}
    (mode v) {-^ mode (of both the universe and its elements) -}
    (Term mode mhom v) {-^ level -} |
  Pi (Binding mode mhom v) |
  Sigma (Binding mode mhom v) |
  EmptyType |
  UnitType
  deriving (Functor, Foldable, Traversable, Generic1)
deriving instance (Functor mode, Functor mhom, Swallows mode (Term mode mhom), Swallows mhom (Term mode mhom)) =>
  Swallows (TypeTerm mode mhom) (Term mode mhom)

data ConstructorTerm (mode :: * -> *) (mhom :: * -> *) (v :: *) =
  ConsUnsafeResize
    (mode v) {-^ Type's mode -}
    (Term mode mhom v) {-^ Type's proper level -}
    (Term mode mhom v) {-^ Type's assigned level -}
    (TypeTerm mode mhom v) {-^ Type -} |
  Lam (Binding mode mhom v) |
  Pair SegmentInfo
    (ModedModality mode mhom v)
    (Term mode mhom v)
    (Term mode mhom v) |
  ConsUnit
  deriving (Functor, Foldable, Traversable, Generic1)
deriving instance (Functor mode, Functor mhom, Swallows mode (Term mode mhom), Swallows mhom (Term mode mhom)) =>
  Swallows (ConstructorTerm mode mhom) (Term mode mhom)

data SmartEliminator (mode :: * -> *) (mhom :: * -> *) (v :: *) =
  SmartElimEnd Raw.ArgSpec |
  SmartElimArg Raw.ArgSpec (Term mode mhom v) |
  SmartElimProj Raw.ProjSpec
  deriving (Functor, Foldable, Traversable, Generic1)
deriving instance (Functor mode, Functor mhom, Swallows mode (Term mode mhom), Swallows mhom (Term mode mhom)) =>
  Swallows (SmartEliminator mode mhom) (Term mode mhom)

data Eliminator (mode :: * -> *) (mhom :: * -> *) (v :: *) =
  ElimUnsafeResize
    (Term mode mhom v) {-^ Type's proper level -}
    (Term mode mhom v) {-^ Type's assigned level -}
    (Term mode mhom v) {-^ Type -} |
  App Raw.ArgSpec (Term mode mhom v) {-^ argument -} |
  ElimPair
    (Binding mode mhom v) {-^ pair's sigma type -} 
    (Term mode mhom (Maybe v)) {-^ motive -}
    (Term mode mhom (Maybe (Maybe v))) {-^ clause -} |
  Fst
    (Binding mode mhom v) {-^ pair's sigma type -} |
  Snd
    (Binding mode mhom v) {-^ pair's sigma type -} |
  ElimEmpty
    (Term mode mhom (Maybe v)) {-^ motive -}
  deriving (Functor, Foldable, Traversable, Generic1)
deriving instance (Functor mode, Functor mhom, Swallows mode (Term mode mhom), Swallows mhom (Term mode mhom)) =>
  Swallows (Eliminator mode mhom) (Term mode mhom)

data TermNV (mode :: * -> *) (mhom :: * -> *) (v :: *) =
  TermCons (ConstructorTerm mode mhom v) |
  TermElim
    (ModedModality mode mhom v) {-^ modality by which the eliminee is used -}
    (Term mode mhom v) {-^ eliminee -}
    (Eliminator mode mhom v) {-^ eliminator -} |
  TermMeta (Compose [] (Term mode mhom) v)
  deriving (Functor, Foldable, Traversable, Generic1)
deriving instance (Functor mode, Functor mhom, Swallows mode (Term mode mhom), Swallows mhom (Term mode mhom)) =>
  Swallows (TermNV mode mhom) (Term mode mhom)

type Term mode mhom = Expr (TermNV mode mhom)

-- | is this useful?
data Type (mode :: * -> *) (mhom :: * -> *) (v :: *) =
  ElType {-^ Constructor'ish -} 
    (Term mode mhom v) {-^ Type's proper level -}
    (TypeTerm mode mhom v) {-^ Type -} |
  ElTerm {-^ Eliminator'ish -}
    (Term mode mhom v) {-^ Type's proper level -}
    (Term mode mhom v) {-^ Type -}
  deriving (Functor, Foldable, Traversable, Generic1)
deriving instance (Functor mode, Functor mhom, Swallows mode (Term mode mhom), Swallows mhom (Term mode mhom)) =>
  Swallows (Type mode mhom) (Term mode mhom)
 
data Pair3 t (a :: ka) (b :: kb) (c :: kc) = Pair3 (t a b c) (t a b c) deriving (Functor, Foldable, Traversable, Generic1)
deriving instance (Swallows (t mode mhom) (Term mode mhom)) => Swallows (Pair3 t mode mhom) (Term mode mhom)



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
