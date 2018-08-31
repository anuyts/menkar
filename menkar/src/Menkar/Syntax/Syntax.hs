{- # LANGUAGE DataKinds, KindSignatures, GADTs, TypeOperators, RankNTypes #-}

module Menkar.Syntax.Syntax where

import Menkar.Syntax.Composable
import GHC.Generics
import qualified Menkar.Raw.Base as Raw
import Data.Functor.Compose

data SegmentInfo = SegmentInfo {name :: String}
data MetaInfo where

data ModedModality (mobj :: * -> *) (mhom :: * -> *) (v :: *) =
  ModedModality {domMode :: mobj v, codMode :: mobj v, modality :: mhom v}
  deriving (Functor, Foldable, Traversable, Generic1)
deriving instance (Functor mobj, Functor mhom, Swallows mobj (Term mobj mhom), Swallows mhom (Term mobj mhom)) =>
  Swallows (ModedModality mobj mhom) (Term mobj mhom)

data Binding (mobj :: * -> *) (mhom :: * -> *) (v :: *) =
  Binding {
    bindingInfo :: SegmentInfo,
    bindingModality :: ModedModality mobj mhom v,
    bindingDomain :: Term mobj mhom v,
    bindingBody :: Term mobj mhom (Maybe v)}
  deriving (Functor, Foldable, Traversable, Generic1)
deriving instance (Functor mobj, Functor mhom, Swallows mobj (Term mobj mhom), Swallows mhom (Term mobj mhom)) =>
  Swallows (Binding mobj mhom) (Term mobj mhom)

data TypeTerm (mobj :: * -> *) (mhom :: * -> *) (v :: *) =
  UniHS {-^ Hofmann-Streicher universe, or at least a universe that classifies its own mode. -}
    (mobj v) {-^ mode (of both the universe and its elements) -}
    (Term mobj mhom v) {-^ level -} |
  Pi (Binding mobj mhom v) |
  Sigma (Binding mobj mhom v) |
  EmptyType |
  UnitType
  deriving (Functor, Foldable, Traversable, Generic1)
deriving instance (Functor mobj, Functor mhom, Swallows mobj (Term mobj mhom), Swallows mhom (Term mobj mhom)) =>
  Swallows (TypeTerm mobj mhom) (Term mobj mhom)

data ConstructorTerm (mobj :: * -> *) (mhom :: * -> *) (v :: *) =
  ConsUnsafeResize
    (mobj v) {-^ Type's mode -}
    (Term mobj mhom v) {-^ Type's proper level -}
    (Term mobj mhom v) {-^ Type's assigned level -}
    (TypeTerm mobj mhom v) {-^ Type -} |
  Lam (Binding mobj mhom v) |
  Pair SegmentInfo
    (ModedModality mobj mhom v)
    (Term mobj mhom v)
    (Term mobj mhom v) |
  ConsUnit
  deriving (Functor, Foldable, Traversable, Generic1)
deriving instance (Functor mobj, Functor mhom, Swallows mobj (Term mobj mhom), Swallows mhom (Term mobj mhom)) =>
  Swallows (ConstructorTerm mobj mhom) (Term mobj mhom)

data Eliminator (mobj :: * -> *) (mhom :: * -> *) (v :: *) =
  ElimUnsafeResize
    (Term mobj mhom v) {-^ Type's proper level -}
    (Term mobj mhom v) {-^ Type's assigned level -}
    (Term mobj mhom v) {-^ Type -} |
  App Raw.ArgSpec (Term mobj mhom v) {-^ argument -} |
  ElimPair
    (Binding mobj mhom v) {-^ pair's sigma type -} 
    (Term mobj mhom (Maybe v)) {-^ motive -}
    (Term mobj mhom (Maybe (Maybe v))) {-^ clause -} |
  Fst
    (Binding mobj mhom v) {-^ pair's sigma type -} |
  Snd
    (Binding mobj mhom v) {-^ pair's sigma type -} |
  ElimEmpty
    (Term mobj mhom (Maybe v)) {-^ motive -}
  deriving (Functor, Foldable, Traversable, Generic1)
deriving instance (Functor mobj, Functor mhom, Swallows mobj (Term mobj mhom), Swallows mhom (Term mobj mhom)) =>
  Swallows (Eliminator mobj mhom) (Term mobj mhom)

data TermNV (mobj :: * -> *) (mhom :: * -> *) (v :: *) =
  TermCons (ConstructorTerm mobj mhom v) |
  TermElim
    (ModedModality mobj mhom v) {-^ modality by which the eliminee is used -}
    (Term mobj mhom v) {-^ eliminee -}
    (Eliminator mobj mhom v) {-^ eliminator -} |
  TermMeta (Compose [] (Term mobj mhom) v)
  deriving (Functor, Foldable, Traversable, Generic1)
deriving instance (Functor mobj, Functor mhom, Swallows mobj (Term mobj mhom), Swallows mhom (Term mobj mhom)) =>
  Swallows (TermNV mobj mhom) (Term mobj mhom)

type Term mobj mhom = Expr (TermNV mobj mhom)

data Type (mobj :: * -> *) (mhom :: * -> *) (v :: *) =
  ElType {-^ Constructor'ish -} 
    (Term mobj mhom v) {-^ Type's proper level -}
    (TypeTerm mobj mhom v) {-^ Type -} |
  ElTerm {-^ Eliminator'ish -}
    (Term mobj mhom v) {-^ Type's proper level -}
    (Term mobj mhom v) {-^ Type -}
  deriving (Functor, Foldable, Traversable, Generic1)
deriving instance (Functor mobj, Functor mhom, Swallows mobj (Term mobj mhom), Swallows mhom (Term mobj mhom)) =>
  Swallows (Type mobj mhom) (Term mobj mhom)
 





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
