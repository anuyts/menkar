{-# LANGUAGE StandaloneDeriving #-}

module Menkar.Raw.Syntax where

import Data.Number.Nat
import Data.String.Utils (replace)
import Data.Hashable
import GHC.Generics

data Opness = NonOp | Op deriving (Show, Eq, Generic, Hashable)

data Name = Name {opnessName :: Opness, stringName :: String} deriving (Eq, Generic, Hashable) --deriving Show

data Qualified a = Qualified [String] a
--deriving instance Show a => Show (Qualified a)

type QName = Qualified Name

data ArgSpec = ArgSpecNext | ArgSpecExplicit | ArgSpecNamed String deriving Show

data ProjSpec = ProjSpecNamed String | ProjSpecNumbered Nat | ProjSpecTail Nat deriving Show

data Eliminator =
  ElimEnd ArgSpec {-^ should not be 'ArgSpecExplicit'.-} |
  ElimArg ArgSpec Expr |
  ElimProj ProjSpec
  -- case; induction
  --deriving Show

data Expr3 =
  ExprQName QName |
  ExprParens Expr |
  ExprNatLiteral Nat |
  ExprImplicit
  --deriving Show

data Elimination = Elimination Expr3 [Eliminator] --deriving Show
addEliminators :: Elimination -> [Eliminator] -> Elimination
addEliminators (Elimination e elims) moreElims = Elimination e (elims ++ moreElims)

data Expr2 =
  ExprElimination Elimination
  --deriving Show

data Operand = OperandTelescope Telescope | OperandExpr Expr2 --deriving Show

data Expr = ExprOps Operand (Maybe (Elimination, Maybe Expr)) --deriving Show

expr3to2 :: Expr3 -> Expr2
expr3to2 e = ExprElimination $ Elimination e []
expr2to1 :: Expr2 -> Expr
expr2to1 e = ExprOps (OperandExpr e) Nothing
expr3to1smart :: Expr3 -> Expr
expr3to1smart (ExprParens e) = e
expr3to1smart ExprImplicit = expr2to1 $ ExprElimination $ Elimination ExprImplicit [ElimEnd ArgSpecNext]
expr3to1smart e = expr2to1 . expr3to2 $ e

-----------------------------------------------------------

{-| One item in the annotation clause. -}
data Annotation = Annotation (Qualified String) [Expr3] --deriving Show

newtype Segment = Segment (Declaration DeclSortSegment) --deriving Show

{-| A bunch of assumptions in accolads. Essentially a dependent telescope. -}
newtype Telescope = Telescope {untelescope :: [Segment]} --deriving Show

data DeclSort =
  DeclSortVal |
  DeclSortModule Bool {-^ Whether it's toplevel. -} |
  DeclSortResolution |
  DeclSortSegment

data DeclNames declSort where
  DeclNamesSegment :: [Maybe Name] {-^ name or underscore -} -> DeclNames DeclSortSegment
  DeclNamesToplevelModule :: Qualified String -> DeclNames (DeclSortModule True)
  DeclNamesModule :: String -> DeclNames (DeclSortModule False)
  DeclNamesVal :: Name -> DeclNames DeclSortVal
  --deriving (Show)

type family DeclContent (declSort :: DeclSort) :: *
type instance DeclContent DeclSortVal = Maybe Expr
type instance DeclContent (DeclSortModule b) = ()
type instance DeclContent DeclSortResolution = Maybe Expr
type instance DeclContent DeclSortSegment = Maybe Expr

data EntryHeader :: DeclSort -> * where
  HeaderModule :: EntryHeader (DeclSortModule b)
  HeaderVal :: EntryHeader DeclSortVal
  HeaderResolution :: EntryHeader DeclSortResolution
  HeaderData :: EntryHeader DeclSortVal
  HeaderCodata :: EntryHeader DeclSortVal

--data EntryHeader = HeaderModule | HeaderVal | HeaderData | HeaderCodata | HeaderResolution deriving Show
headerKeyword :: EntryHeader declSort -> String
headerKeyword HeaderModule = "module"
headerKeyword HeaderVal = "val"
headerKeyword HeaderData = "data"
headerKeyword HeaderCodata = "codata"
headerKeyword HeaderResolution = "resolution"

{-| The left hand side of a genuine entry, or the content of a cell of a telescope.
    For entries, there is typically one name. -}
data Declaration declSort = Declaration {
  decl'annotations :: [Annotation],
  decl'names :: DeclNames declSort,
  decl'telescope :: Telescope,
  decl'content :: DeclContent declSort} --deriving Show

data RHS declSort where
  RHSModule :: [AnyEntry] -> RHS (DeclSortModule b)
  RHSVal :: Expr -> RHS DeclSortVal
  --RHSResolution
  --deriving Show

coerceRHSToplevel :: RHS (DeclSortModule b1) -> RHS (DeclSortModule b2)
coerceRHSToplevel (RHSModule entries) = RHSModule entries

data Entry declSort where
  LREntry :: EntryHeader declSort -> Declaration declSort -> RHS declSort -> Entry declSort
  --deriving Show

data AnyEntry where
  AnyEntry :: Entry declSort -> AnyEntry

--newtype Entry = EntryLR LREntry --deriving Show

newtype File = File (Entry (DeclSortModule True)) --deriving Show

wrapInModules :: [String] -> Entry (DeclSortModule False) -> Entry (DeclSortModule False)
wrapInModules [] entry = entry
wrapInModules (moduleName:moduleNames) entry =
  LREntry HeaderModule lhs rhs
  where lhs = Declaration {
          decl'annotations = [],
          decl'names = DeclNamesModule $ moduleName,
          decl'telescope = Telescope [],
          decl'content = ()
          }
        rhs = RHSModule [AnyEntry $ wrapInModules moduleNames entry]

file2nestedModules :: File -> Entry (DeclSortModule False)
file2nestedModules (File toplevelmodule@(LREntry HeaderModule lhs rhs)) =
  let DeclNamesToplevelModule (Qualified moduleNames string) = decl'names lhs
      lhs' = Declaration {
        decl'annotations = decl'annotations lhs,
        decl'names = DeclNamesModule $ string,
        decl'telescope = decl'telescope lhs,
        decl'content = ()
        }
      modul = LREntry HeaderModule lhs' (coerceRHSToplevel rhs)
  in wrapInModules moduleNames modul
