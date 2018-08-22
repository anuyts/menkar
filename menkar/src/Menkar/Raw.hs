{-# LANGUAGE StandaloneDeriving #-}

module Menkar.Raw where

import Data.Number.Nat
import Text.PrettyPrint.Leijen
import Data.String.Utils (replace)

--data Module = Module [Entry] deriving (Show)

showshowdoc :: Doc -> String
showshowdoc doc = replace "\\n" "\t\t\\n\\\n\\" $ show $ displayS (renderPretty 1.0 100 doc) ""

data Opness = NonOp | Op deriving Show

data Name = Name Opness String deriving Show
instance Pretty Name where
  pretty = undefined

data Qualified a = Qualified [String] a
deriving instance Show a => Show (Qualified a)
instance Pretty a => Pretty (Qualified a) where
  pretty = undefined

--data QName = QName [String] Name deriving Show
type QName = Qualified Name
{-
renderQName :: [String] -> ShowS
renderQName [] tail = "<EMPTY QNAME>" ++ tail
renderQName [name] tail = name ++ tail
renderQName (name : names) tail = name ++ ('.' : (renderQName names tail))
-}
--instance Pretty QName where
--  pretty = undefined
  --pretty (QName names) = encloseSep empty empty dot (map text names)
--instance Show QName where
--  show qname = "(quickParse qIdentifier " ++ (showshowdoc $ pretty qname) ++ ")"

data ArgSpec = ArgSpecNext | ArgSpecVisible | ArgSpecNamed String deriving Show

--data Argument = Argument ArgSpec Expr

data ProjSpec = ProjSpecNamed String | ProjSpecNumbered Nat | ProjSpecTail Nat deriving Show

data Eliminator =
  ElimEnd (Maybe ArgSpec) |
  ElimArg ArgSpec Expr |
  ElimProj ProjSpec
  -- case; induction
  deriving Show

data Expr3 =
  ExprQName QName |
  ExprParens Expr |
  ExprNatLiteral Nat |
  ExprImplicit
  deriving Show

data Elimination = Elimination Expr3 [Eliminator] deriving Show

--data TeleThing = TeleLambda Expr | TelePi Expr | TeleSigma Expr
--  deriving Show

data Expr2 =
  ExprElimination Elimination
  deriving Show
expr3to2 :: Expr3 -> Expr2
expr3to2 e = ExprElimination $ Elimination e []

data Operand = OperandTelescope Telescope | OperandExpr Expr2 deriving Show

data Expr = ExprOps Operand (Maybe (Elimination, Maybe Expr)) deriving Show
instance Pretty Expr where
  pretty = undefined
expr2to1 :: Expr2 -> Expr
expr2to1 e = ExprOps (OperandExpr e) Nothing

{-
data Atom =
  AtomQName QName |
  AtomParens Expr |
  AtomDot |
  AtomSegment Segment |
  AtomNatLiteral Nat
instance Pretty Atom where
  pretty (AtomQName qname) = pretty qname
  pretty (AtomParens expr) = parens $ pretty expr
  pretty AtomDot = dot
  pretty (AtomSegment segment) = pretty segment
  pretty (AtomNatLiteral n) = text $ show n
instance Show Atom where
  show atom = "(quickParse atom " ++ (showshowdoc $ pretty atom) ++ ")"

data Expr = Expr [Atom]
instance Pretty Expr where
  pretty (Expr atoms) = encloseSep empty empty space (map pretty atoms)
instance Show Expr where
  show expr = "(quickParse expr " ++ (showshowdoc $ pretty expr) ++ ")"
-}

-----------------------------------------------------------

{-| One item in the annotation clause. -}
data Annotation = Annotation (Qualified String) (Maybe Expr)
  --{-| An annotation that is just an unqualified identifier, e.g. "irr" or "~" -}
  --AnnotationAtomic String |
  --{-| An annotation written in Haskell. The string the Haskell code, without brackets. -}
  --AnnotationHaskell String
instance Pretty Annotation where
  pretty (Annotation qname Nothing) = pretty qname
  pretty (Annotation qname (Just expr)) = parens $ pretty qname <> space <> pretty expr
instance Show Annotation where
  show annot = "(quickParse annotation " ++ (showshowdoc $ pretty annot) ++ ")"

prettyAnnotationBrackets :: Annotation -> Doc
prettyAnnotationBrackets (Annotation qname Nothing) = brackets $ pretty qname
prettyAnnotationBrackets (Annotation qname (Just expr)) = brackets $ pretty qname <> space <> pretty expr

prettyAnnotationClause :: [Annotation] -> Doc
prettyAnnotationClause annots = (encloseSep empty (text " |") space (map pretty annots))

data Segment = Segment LHS -- | SegmentConstraint LHS
instance Pretty Segment where
  pretty (Segment lhs) = braces $ case (namesLHS lhs, typeLHS lhs) of
    (NoNameForConstraint, Just expr) ->
      prettyAnnotationClause (annotationsLHS lhs)
      </> pretty (contextLHS lhs)
      </> text "-:"
      </> pretty expr
    (SomeNamesForTelescope names, Just expr) ->
      prettyAnnotationClause (annotationsLHS lhs)
      </> encloseSep empty empty space (undefined {-map text names-})
      </> pretty (contextLHS lhs)
      </> text ":"
      </> pretty expr
    (SomeNamesForTelescope names, Nothing) ->
      prettyAnnotationClause (annotationsLHS lhs)
      </> encloseSep empty empty space (undefined {-map text names-})
      </> pretty (contextLHS lhs)
    _ -> text "<ERRONEOUS SEGMENT>:" </> (parens $ pretty lhs)
instance Show Segment where
  show segment = "(quickParse segment " ++ (showshowdoc $ pretty segment) ++ ")"

{-| A bunch of assumptions in accolads. Essentially a dependent telescope. -}
data Telescope = Telescope [Segment]
instance Pretty Telescope where
  pretty (Telescope segments) = encloseSep empty empty softline (map pretty segments)
instance Show Telescope where
  show telescope = "(quickParse telescope \n" ++ (showshowdoc $ pretty telescope) ++ ")"

data LHSNames =
  SomeNamesForTelescope [Maybe Name] -- name or underscore
  | QNameForEntry QName
  | NoNameForConstraint
  deriving (Show)
instance Pretty LHSNames where
  pretty (SomeNamesForTelescope names) = encloseSep empty empty space (undefined {-map text names-})
  pretty (QNameForEntry qname) = pretty qname
  pretty (NoNameForConstraint) = text $ "<NoNameForConstraint>"
  
data EntryHeader = HeaderModule | HeaderVal | HeaderData | HeaderCodata | HeaderResolution deriving Show
headerKeyword :: EntryHeader -> String
headerKeyword HeaderModule = "module"
headerKeyword HeaderVal = "val"
headerKeyword HeaderData = "data"
headerKeyword HeaderCodata = "codata"
headerKeyword HeaderResolution = "resolution"
instance Pretty EntryHeader where
  pretty header = text $ headerKeyword header

{-| The left hand side of a genuine entry, or the content of a cell of a telescope.
    For entries, there is typically one name. -}
data LHS = LHS {
  annotationsLHS :: [Annotation],
  namesLHS :: LHSNames,
  contextLHS :: Telescope,
  typeLHS :: Maybe Expr}
instance Pretty LHS where
  pretty lhs =
    encloseSep empty empty space (map prettyAnnotationBrackets $ annotationsLHS lhs) </>
    pretty (namesLHS lhs) <> (
      line <>
      pretty (contextLHS lhs) <> case typeLHS lhs of
          Nothing -> empty
          Just expr -> empty </> char ':' </> pretty expr
    )
instance Show LHS where
  show lhs = "(quickParse lhs \n" ++ (showshowdoc $ pretty lhs) ++ ")"

data RHS =
  RHSModule [Entry]
  | RHSVal Expr
  | RHSResolution
instance Pretty RHS where
  pretty (RHSModule entries) = text "where"
                               <> space
                               <> encloseSep (lbrace <> line) (line <> rbrace) line (map pretty entries)
  pretty (RHSVal expr) = char '=' </> pretty expr
  pretty (RHSResolution) = empty
instance Show RHS where
  show rhs@(RHSModule _) = "(quickparse (rhs Raw.HeaderModule) \n" ++ (showshowdoc $ pretty rhs) ++ ")"
  show rhs@(RHSVal _) = "(quickparse (rhs Raw.HeaderVal) \n" ++ (showshowdoc $ pretty rhs) ++ ")"
  show rhs@(RHSResolution) = "(quickparse (rhs Raw.HeaderResolution) \n" ++ (showshowdoc $ pretty rhs) ++ ")"

data LREntry = LREntry EntryHeader LHS RHS
instance Pretty LREntry where
  pretty (LREntry header lhs rhs) = pretty header </> pretty lhs <> line <> pretty rhs
instance Show LREntry where
  show entry = "(quickParse lrEntry \n" ++ (showshowdoc $ pretty entry) ++ ")"

data Entry = EntryLR LREntry
instance Pretty Entry where
  pretty (EntryLR lrEntry) = pretty lrEntry
instance Show Entry where
  show entry = "(quickParse entry \n" ++ (showshowdoc $ pretty entry) ++ ")"
  
data File = File LREntry
instance Pretty File where
  pretty (File lrEntry) = pretty lrEntry
instance Show File where
  show file = "(quickParse file \n" ++ (showshowdoc $ pretty file) ++ ")"
