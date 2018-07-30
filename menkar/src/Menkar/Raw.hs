module Menkar.Raw where

import Data.Number.Nat

--data Module = Module [Entry] deriving (Show)

data QName = QName [String] deriving (Show)

data Atom =
  AtomQName QName |
  AtomParens Expr |
  AtomDot |
  AtomTelescope Telescope |
  AtomNatLiteral Nat
  deriving (Show)

data Expr = Expr [Atom] deriving (Show)

-----------------------------------------------------------

{-| One item in the annotation clause. -}
data Annotation = Annotation QName (Maybe Expr)
  --{-| An annotation that is just an unqualified identifier, e.g. "irr" or "~" -}
  --AnnotationAtomic String |
  --{-| An annotation written in Haskell. The string the Haskell code, without brackets. -}
  --AnnotationHaskell String
  deriving (Show)

data Segment = Segment LHS -- | SegmentConstraint LHS
  deriving (Show)
{-| A bunch of assumptions in accolads. Essentially a dependent telescope. -}
data Telescope = Telescope [Segment] deriving (Show)

data LHSNames =
  SomeNamesForTelescope [String] |
  QNameForEntry QName |
  NoNameForConstraint
  deriving (Show)
{-| The left hand side of a genuine entry, or the content of a cell of a telescope.
    For entries, there is typically one name. -}
data LHS = LHS {
  annotationsLHS :: [Annotation],
  namesLHS :: LHSNames,
  contextLHS :: Telescope,
  typeLHS :: Maybe Expr} deriving (Show)

data RHS = RHSModule [Entry] deriving (Show)
data LREntry = LREntry LHS RHS deriving (Show)

data Entry = EntryLR LREntry deriving (Show)
data File = File LREntry deriving (Show)
