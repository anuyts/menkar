{- # LANGUAGE DataKinds, KindSignatures, GADTs, TypeOperators, RankNTypes #-}

module Menkar.Syntax.Syntax where

import Menkar.Syntax.Composable
import GHC.Generics
import qualified Menkar.Raw.Base as Raw
import Data.Functor.Compose

{- Segment info will have to depend on v, because 'resolves' annotations have variables -}
data SegmentInfo = SegmentInfo {name :: String}
data MetaInfo where

data ModedModality (mode :: * -> *) (modty :: * -> *) (v :: *) =
  ModedModality {domMode :: mode v, codMode :: mode v, modality :: modty v}
  deriving (Functor, Foldable, Traversable, Generic1)
deriving instance (Functor mode, Functor modty, Swallows mode (Term mode modty), Swallows modty (Term mode modty)) =>
  Swallows (ModedModality mode modty) (Term mode modty)

data Segment (t :: (* -> *) -> (* -> *) -> * -> *) (mode :: * -> *) (modty :: * -> *) (v :: *) =
  Segment {
    segmentInfo :: SegmentInfo,
    segmentModality :: ModedModality mode modty v,
    segmentType :: t mode modty v
  }
  deriving (Functor, Foldable, Traversable, Generic1)
deriving instance (
    Functor mode,
    Functor modty,
    Swallows mode (Term mode modty),
    Swallows modty (Term mode modty),
    Swallows (t mode modty) (Term mode modty)
  ) => Swallows (Segment t mode modty) (Term mode modty)

data Binding (mode :: * -> *) (modty :: * -> *) (v :: *) =
  Binding {
    bindingSegment :: Segment Type mode modty v,
    bindingBody :: Term mode modty (Maybe v)
  }
  deriving (Functor, Foldable, Traversable, Generic1)
deriving instance (Functor mode, Functor modty, Swallows mode (Term mode modty), Swallows modty (Term mode modty)) =>
  Swallows (Binding mode modty) (Term mode modty)

data TypeTerm (mode :: * -> *) (modty :: * -> *) (v :: *) =
  UniHS {-^ Hofmann-Streicher universe, or at least a universe that classifies its own mode. -}
    (mode v) {-^ mode (of both the universe and its elements) -}
    (Term mode modty v) {-^ level -} |
  Pi (Binding mode modty v) |
  Sigma (Binding mode modty v) |
  EmptyType |
  UnitType
  deriving (Functor, Foldable, Traversable, Generic1)
deriving instance (Functor mode, Functor modty, Swallows mode (Term mode modty), Swallows modty (Term mode modty)) =>
  Swallows (TypeTerm mode modty) (Term mode modty)

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
deriving instance (Functor mode, Functor modty, Swallows mode (Term mode modty), Swallows modty (Term mode modty)) =>
  Swallows (ConstructorTerm mode modty) (Term mode modty)

data SmartEliminator (mode :: * -> *) (modty :: * -> *) (v :: *) =
  SmartElimEnd Raw.ArgSpec |
  SmartElimArg Raw.ArgSpec (Term mode modty v) |
  SmartElimProj Raw.ProjSpec
  deriving (Functor, Foldable, Traversable, Generic1)
deriving instance (Functor mode, Functor modty, Swallows mode (Term mode modty), Swallows modty (Term mode modty)) =>
  Swallows (SmartEliminator mode modty) (Term mode modty)

data Eliminator (mode :: * -> *) (modty :: * -> *) (v :: *) =
  ElimUnsafeResize
    (Term mode modty v) {-^ Type's proper level -}
    (Term mode modty v) {-^ Type's assigned level -}
    (Term mode modty v) {-^ Type -} |
  App Raw.ArgSpec (Term mode modty v) {-^ argument -} |
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
deriving instance (Functor mode, Functor modty, Swallows mode (Term mode modty), Swallows modty (Term mode modty)) =>
  Swallows (Eliminator mode modty) (Term mode modty)

data TermNV (mode :: * -> *) (modty :: * -> *) (v :: *) =
  TermCons (ConstructorTerm mode modty v) |
  TermElim
    (ModedModality mode modty v) {-^ modality by which the eliminee is used -}
    (Term mode modty v) {-^ eliminee -}
    (Eliminator mode modty v) {-^ eliminator -} |
  TermMeta (Compose [] (Term mode modty) v)
  deriving (Functor, Foldable, Traversable, Generic1)
deriving instance (Functor mode, Functor modty, Swallows mode (Term mode modty), Swallows modty (Term mode modty)) =>
  Swallows (TermNV mode modty) (Term mode modty)

type Term mode modty = Expr (TermNV mode modty)

-- | is this useful?
data Type (mode :: * -> *) (modty :: * -> *) (v :: *) =
  ElType {-^ Constructor'ish -} 
    (Term mode modty v) {-^ Type's proper level -}
    (TypeTerm mode modty v) {-^ Type -} |
  ElTerm {-^ Eliminator'ish -}
    (Term mode modty v) {-^ Type's proper level -}
    (Term mode modty v) {-^ Type -}
  deriving (Functor, Foldable, Traversable, Generic1)
deriving instance (Functor mode, Functor modty, Swallows mode (Term mode modty), Swallows modty (Term mode modty)) =>
  Swallows (Type mode modty) (Term mode modty)
 
data Pair3 t (a :: ka) (b :: kb) (c :: kc) = Pair3 {fst3 :: t a b c, snd3 :: t a b c} deriving (Functor, Foldable, Traversable, Generic1)
deriving instance (Swallows (t mode modty) (Term mode modty)) => Swallows (Pair3 t mode modty) (Term mode modty)



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
