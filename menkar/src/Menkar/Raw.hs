module Menkar.Raw where

--data Module = Module [Entry] deriving (Show)

data Expr =
  ExprParens [Expr] |
  ExprDot |
  ExprTelescope Telescope |
  ExprPseudoArg String
  deriving (Show)

-----------------------------------------------------------

{-| A pseudo-entry (todo) -}
data PseudoEntry = PseudoEntry deriving (Show)

{-| One item in the annotation clause. -}
data Annotation =
  {-| An annotation that is just an unqualified identifier, e.g. "irr" or "~" -}
  AnnotationAtomic String |
  {-| An annotation written in Haskell. The string the Haskell code, without brackets. -}
  AnnotationHaskell String
  deriving (Show)

data Segment = Segment LHS -- | SegmentPseudo PseudoLHS
  deriving (Show)
{-| A bunch of assumptions in accolads. Essentially a dependent telescope. -}
data Telescope = Telescope [Segment] deriving (Show)

data LHSNames =
  OneNameForEntry String |
  ManyNamesForVariables [String] |
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
data GenuineEntry = GenuineEntry LHS RHS deriving (Show)

data Entry = EntryGenuine GenuineEntry | EntryPseudo PseudoEntry deriving (Show)
data File = File [PseudoEntry] GenuineEntry deriving (Show)
