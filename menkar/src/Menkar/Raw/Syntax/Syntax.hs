{-# LANGUAGE StandaloneDeriving #-}

module Menkar.Raw.Syntax.Syntax where

import Menkar.System.Basic
import Menkar.System.Raw
import Menkar.Basic.Syntax

import Data.Number.Nat
import Data.String.Utils (replace)
import Data.Hashable
import Data.Kind
import GHC.Generics

data Eliminator (sys :: KSys) =
  ElimDots |
  --ElimEnd ArgSpec {-^ should not be 'ArgSpecExplicit'.-} |
  ElimArg ArgSpec (Expr sys) |
  ElimProj ProjSpec
  -- case; induction
  --deriving Show

data ExprC (sys :: KSys) =
  ExprQName QName |
  ExprParens (Expr sys) |
  ExprNatLiteral Nat |
  ExprImplicit |
  ExprGoal String |
  ExprSys (SysExprC sys)
  --deriving Show

data Elimination (sys :: KSys) = Elimination (ExprC sys) [Eliminator sys] --deriving Show
addEliminators :: forall sys . Elimination sys -> [Eliminator sys] -> Elimination sys
addEliminators (Elimination e elims) moreElims = Elimination e (elims ++ moreElims)

data ExprB (sys :: KSys) =
  ExprElimination (Elimination sys)
  --deriving Show

data Operand (sys :: KSys) =
  OperandTelescope (Telescope sys) |
  OperandExpr (ExprB sys) --deriving Show

data Expr (sys :: KSys) =
  ExprOps (Operand sys) (Maybe (Elimination sys, Maybe (Expr sys))) --deriving Show

exprCtoB :: ExprC sys -> ExprB sys
exprCtoB e = ExprElimination $ Elimination e []
exprBtoA :: ExprB sys -> Expr sys
exprBtoA e = ExprOps (OperandExpr e) Nothing
exprCtoA :: ExprC sys -> Expr sys
exprCtoA = exprBtoA . exprCtoB
exprCtoAsmart :: ExprC sys -> Expr sys
exprCtoAsmart (ExprParens e) = e
--exprCto1smart ExprImplicit = exprBtoA $ ExprElimination $ Elimination ExprImplicit [ElimEnd ArgSpecNext]
exprCtoAsmart e = exprBtoA . exprCtoB $ e

-----------------------------------------------------------

{-| One item in the annotation clause. -}
data Annotation (sys :: KSys) = Annotation (Qualified String) (Maybe (Expr sys)) --deriving Show

newtype Segment sys = Segment (Declaration sys DeclSortSegment) --deriving Show

{-| A bunch of assumptions in accolads. Essentially a dependent telescope. -}
newtype Telescope sys = Telescope {untelescope :: [Segment sys]} --deriving Show

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

class CanBeTyped (declSort :: DeclSort) where

instance CanBeTyped DeclSortVal where
instance CanBeTyped DeclSortResolution where
instance CanBeTyped DeclSortSegment where

data DeclContent sys (declSort :: DeclSort) where
  DeclContent :: CanBeTyped declSort => Expr sys -> DeclContent sys declSort
  DeclContentEmpty :: DeclContent sys declSort

data EntryHeader :: DeclSort -> * where
  HeaderToplevelModule :: EntryHeader (DeclSortModule True)
  HeaderModule :: EntryHeader (DeclSortModule False)
  HeaderVal :: EntryHeader DeclSortVal
  HeaderResolution :: EntryHeader DeclSortResolution
  HeaderData :: EntryHeader DeclSortVal
  HeaderCodata :: EntryHeader DeclSortVal

data AnyEntryHeader where
  AnyEntryHeader :: EntryHeader declSort -> AnyEntryHeader

--data EntryHeader = HeaderModule | HeaderVal | HeaderData | HeaderCodata | HeaderResolution deriving Show
headerKeyword :: EntryHeader declSort -> String
headerKeyword HeaderToplevelModule = "module"
headerKeyword HeaderModule = "module"
headerKeyword HeaderVal = "val"
headerKeyword HeaderData = "data"
headerKeyword HeaderCodata = "codata"
headerKeyword HeaderResolution = "resolution"

{-| The left hand side of a genuine entry, or the content of a cell of a telescope.
    For entries, there is typically one name. -}
data Declaration sys declSort = Declaration {
  decl'annotations :: [Annotation sys],
  decl'names :: DeclNames declSort,
  decl'telescope :: Telescope sys,
  decl'content :: DeclContent sys declSort} --deriving Show

data RHS sys declSort where
  RHSModule :: [AnyEntry sys] -> RHS sys (DeclSortModule b)
  RHSVal :: Expr sys -> RHS sys DeclSortVal
  --RHSResolution
  --deriving Show

coerceRHSToplevel :: RHS sys (DeclSortModule b1) -> RHS sys (DeclSortModule b2)
coerceRHSToplevel (RHSModule entries) = RHSModule entries

data Entry sys declSort = EntryLR {
  entry'header :: EntryHeader declSort,
  entry'lhs :: Declaration sys declSort,
  entry'rhs :: RHS sys declSort}
  --deriving Show

data AnyEntry sys where
  AnyEntry :: Entry sys declSort -> AnyEntry sys

--newtype Entry = EntryLR EntryLR --deriving Show

newtype File sys = File (Entry sys (DeclSortModule True)) --deriving Show

wrapInModules :: [String] -> Entry sys (DeclSortModule False) -> Entry sys (DeclSortModule False)
wrapInModules [] entry = entry
wrapInModules (moduleName:moduleNames) entry =
  EntryLR HeaderModule lhs rhs
  where lhs = Declaration {
          decl'annotations = [],
          decl'names = DeclNamesModule $ moduleName,
          decl'telescope = Telescope [],
          decl'content = DeclContentEmpty
          }
        rhs = RHSModule [AnyEntry $ wrapInModules moduleNames entry]

file2nestedModules :: File sys -> Entry sys (DeclSortModule False)
file2nestedModules (File toplevelmodule@(EntryLR HeaderToplevelModule lhs rhs)) =
  let DeclNamesToplevelModule (Qualified moduleNames string) = decl'names lhs
      lhs' = Declaration {
        decl'annotations = decl'annotations lhs,
        decl'names = DeclNamesModule $ string,
        decl'telescope = decl'telescope lhs,
        decl'content = DeclContentEmpty
        }
      modul = EntryLR HeaderModule lhs' (coerceRHSToplevel rhs)
  in wrapInModules moduleNames modul
