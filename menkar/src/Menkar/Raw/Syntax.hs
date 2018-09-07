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

data ArgSpec = ArgSpecNext | ArgSpecVisible | ArgSpecNamed String deriving Show

data ProjSpec = ProjSpecNamed String | ProjSpecNumbered Nat | ProjSpecTail Nat deriving Show

data Eliminator =
  ElimEnd ArgSpec {-^ should not be 'ArgSpecVisible'.-} |
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

newtype Segment = Segment LHS --deriving Show

{-| A bunch of assumptions in accolads. Essentially a dependent telescope. -}
newtype Telescope = Telescope {untelescope :: [Segment]} --deriving Show

data LHSNames =
  SomeNamesForTelescope [Maybe Name] -- name or underscore
  | QNameForEntry QName
  | NoNameForConstraint
  --deriving (Show)

data EntryHeader = HeaderModule | HeaderVal | HeaderData | HeaderCodata | HeaderResolution deriving Show
headerKeyword :: EntryHeader -> String
headerKeyword HeaderModule = "module"
headerKeyword HeaderVal = "val"
headerKeyword HeaderData = "data"
headerKeyword HeaderCodata = "codata"
headerKeyword HeaderResolution = "resolution"

{-| The left hand side of a genuine entry, or the content of a cell of a telescope.
    For entries, there is typically one name. -}
data LHS = LHS {
  annotationsLHS :: [Annotation],
  namesLHS :: LHSNames,
  contextLHS :: Telescope,
  typeLHS :: Maybe Expr} --deriving Show

data RHS =
  RHSModule [Entry]
  | RHSVal Expr
  | RHSResolution
  --deriving Show

data LREntry = LREntry EntryHeader LHS RHS --deriving Show

newtype Entry = EntryLR LREntry --deriving Show

newtype File = File LREntry --deriving Show

wrapInModules :: [String] -> Entry -> Entry
wrapInModules [] entry = entry
wrapInModules (moduleName:moduleNames) entry =
  EntryLR $ LREntry HeaderModule lhs rhs
  where lhs = LHS {
          annotationsLHS = [],
          namesLHS = QNameForEntry $ Qualified [] $ Name NonOp moduleName,
          contextLHS = Telescope [],
          typeLHS = Nothing
          }
        rhs = RHSModule [wrapInModules moduleNames entry]

file2nestedModules :: File -> Entry
file2nestedModules (File entry@(LREntry header lhs rhs)) =
  let QNameForEntry (Qualified moduleNames name) = namesLHS lhs
      entry' = EntryLR $ LREntry header (lhs {namesLHS = QNameForEntry $ Qualified [] name}) rhs
  in wrapInModules moduleNames entry'
