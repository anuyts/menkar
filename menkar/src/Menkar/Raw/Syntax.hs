{-# LANGUAGE StandaloneDeriving #-}

module Menkar.Raw.Syntax where

import Data.Number.Nat
import Data.String.Utils (replace)

data Opness = NonOp | Op deriving Show

data Name = Name Opness String --deriving Show

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
expr3to2 :: Expr3 -> Expr2
expr3to2 e = ExprElimination $ Elimination e []

data Operand = OperandTelescope Telescope | OperandExpr Expr2 --deriving Show

data Expr = ExprOps Operand (Maybe (Elimination, Maybe Expr)) --deriving Show
expr2to1 :: Expr2 -> Expr
expr2to1 e = ExprOps (OperandExpr e) Nothing

-----------------------------------------------------------

{-| One item in the annotation clause. -}
data Annotation = Annotation (Qualified String) (Maybe Expr) --deriving Show

data Segment = Segment LHS --deriving Show

{-| A bunch of assumptions in accolads. Essentially a dependent telescope. -}
data Telescope = Telescope {untelescope :: [Segment]} --deriving Show

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

data Entry = EntryLR LREntry --deriving Show

data File = File LREntry --deriving Show
