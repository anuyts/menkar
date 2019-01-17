{-# LANGUAGE FlexibleContexts, FlexibleInstances, ApplicativeDo #-}

module Menkar.Parser where

import qualified Text.Megaparsec as MP
import qualified Text.Megaparsec.Char as MP
--import qualified Text.Megaparsec.Expr as MP
import qualified Menkar.Raw as Raw
import qualified Menkar.PrettyPrint.Raw as Raw

import qualified Text.Megaparsec.Char.Lexer as MPL

import Control.Monad.Identity
import Control.Applicative
import Data.Char
import Data.Number.Nat
import Data.Maybe
import Data.Void
--import Data.Ord

-- Testing -------------------------------------------------

type TestParser = MP.Parsec ParseError String
instance CanParse (MP.ParsecT ParseError String Identity)

testparse :: String -> IO (Either (MP.ParseErrorBundle String ParseError) Raw.File)
testparse filename = do
  let path = "Menkar/code-examples/" ++ filename
  code <- readFile path
  return $ MP.parse file path code

quickParse :: MP.Parsec ParseError String a -> String -> a
quickParse parser code = case MP.parse parser "quick" code of
  Left e -> error $ show e
  Right a -> a

parse :: MP.Parsec ParseError String a -> String -> String -> Either (MP.ParseErrorBundle String ParseError) a
parse parser path code = MP.parse parser path code

-- ParseError ----------------------------------------------

type ParseError = Void
{-
data ParseError
instance Eq ParseError where
  e == e' = True
instance Ord ParseError where
  compare e e' = EQ
instance Show ParseError where
  show e = "ERROR"
-}

-- CanParse ------------------------------------------------

class (MP.MonadParsec ParseError String m) => CanParse m

(<?|>) :: CanParse m => m a -> m a -> m a
p <?|> q = (MP.try p) <|> q

optionalTry :: CanParse m => m a -> m (Maybe a)
optionalTry p = optional (MP.try p)

manyTry :: CanParse m => m a -> m [a]
manyTry = many . MP.try

someTry :: CanParse m => m a -> m [a]
someTry = some . MP.try

someSep :: CanParse m => m () -> m a -> m [a]
someSep sep p = (:) <$> (optional sep *> p) <*> manyTry (sep *> p) <* optional sep

manySep :: CanParse m => m () -> m a -> m [a]
manySep sep p = ([] <$ optionalTry sep) <|> someSep sep p

infixl 3 <?|>

-- characters ----------------------------------------------

data CharType =
  SpaceChar | LetterChar | DigitChar | LooseChar | QuestChar | MiscChar | OpenChar | CloseChar
  deriving (Show, Eq)

looseChars :: [Char]
looseChars = "|_`."

describeCharType :: CharType -> String
describeCharType ct = case ct of
  SpaceChar -> "whitespace character (unicode)"
  LetterChar -> "letter character (unicode)"
  DigitChar -> "digit"
  LooseChar -> "one of " ++ looseChars
  QuestChar -> "question mark"
  MiscChar -> "miscellaneous unicode character"
  OpenChar -> "opening delimiter (unicode)"
  CloseChar -> "closing delimiter (unicode)"

charType :: Char -> CharType
charType c
  | isSpace c = SpaceChar
  | isDigit c = DigitChar
  | isLetter c = LetterChar
  | elem c looseChars = LooseChar
  | c == '?' = QuestChar
  | otherwise = case generalCategory c of
      OpenPunctuation -> OpenChar
      ClosePunctuation -> CloseChar
      _ -> MiscChar

{-
isFirstNameChar :: Char -> Bool
isFirstNameChar c = case charType c of
  LetterChar -> True
  OpChar -> True
  _ -> Falsec
-}
{-
isNameChar :: Char -> Bool
isNameChar c = case charType c of
  LetterChar -> True
  DigitChar -> True
  MiscChar -> True
  _ -> False
-}

-- keywords ------------------------------------------------

keywords :: [String]
keywords = [ ":"     -- typing
           , "="     -- assignment
           , "annotation"
           , "case"
           , "cocase"
           , "codata"
           , "comatch"
           , "constructor"
           , "data"
           , "do"
           , "field"
           , "import"
           , "match"
           , "module"
           , "open"
           , "resolution"
           , "return"
           , "val"
           , "where"
           --, "-:"    -- typing propositions
           --, "->"    -- function type
           --, "><"    -- sigma type
           --, "Uni"   -- universe
           --, "?"     -- for Glue etc.
           --, ">"    -- mapsto
           --, "<"    -- mapsfrom
           ]

-- basic subparsers ----------------------------------------

eof :: CanParse m => m ()
eof = MP.eof

lineComment :: CanParse m => m ()
lineComment = MPL.skipLineComment "//"
blockComment :: CanParse m => m ()
blockComment = MPL.skipBlockCommentNested "/*" "*/"
comment :: CanParse m => m ()
comment = lineComment <|> blockComment
someWhitespace :: CanParse m => m ()
someWhitespace = MP.space1

{-| Consumes zero or more whitespace characters, line or block comments -}
manySpace :: CanParse m => m ()
manySpace = MP.skipMany $ MP.choice [MP.hidden someWhitespace, MP.hidden comment]
{-| Consumes one or more whitespace characters, line or block comments -}
someSpace :: CanParse m => m ()
someSpace = MP.label "whitespace" $ MP.skipSome $ MP.choice [MP.hidden someWhitespace, MP.hidden comment]

socialChar :: CanParse m => m Char
socialChar = charByType LetterChar <|> charByType DigitChar <|> charByType LooseChar
         <|> charByType QuestChar <|> charByType MiscChar

{-| 'lexeme p' consumes 'p', then 'manySpace'. -}
lexeme :: CanParse m => m a -> m a
lexeme p = p <* manySpace
{-| 'loneLexeme p' consumes 'p', then 'someSpace'. -}
loneLexeme :: CanParse m => m a -> m a
loneLexeme p = p <* MP.notFollowedBy socialChar <* manySpace

{-| Consumes and returns the specified string.
    DO NOT USE THIS FOR KEYWORDS, lest "ifbla" will be parsed as "if bla".
    Use for "|", ",". -}
symbol :: CanParse m => String -> m String
symbol = lexeme . MP.string

pipe :: CanParse m => m ()
pipe = void $ symbol "|"

--tickPrecise :: CanParse m => m ()
--tickPrecise = void $ MP.string "`"
underscorePrecise :: CanParse m => m ()
underscorePrecise = void $ MP.string "_"
dotPrecise :: CanParse m => m ()
dotPrecise = void $ MP.string "."
questionMarkPrecise :: CanParse m => m ()
questionMarkPrecise = void $ MP.string "?"

loneUnderscore :: CanParse m => m ()
loneUnderscore = loneLexeme underscorePrecise
loneDot :: CanParse m => m ()
loneDot = loneLexeme dotPrecise
loneDots :: CanParse m => m ()
loneDots = loneLexeme . void $ MP.string "..."

parens :: CanParse m => m a -> m a
parens = MP.between (symbol "(") (symbol ")")

accols :: CanParse m => m a -> m a
accols = MP.between (symbol "{") (symbol "}")

brackets :: CanParse m => m a -> m a
brackets = MP.between (symbol "[") (symbol "]")

ticks :: CanParse m => m a -> m a
ticks = MP.between (symbol "`") (symbol "`")

charByType :: CanParse m => CharType -> m Char
charByType ct = MP.label (describeCharType ct) $ MP.satisfy (\ c -> charType c == ct)

nameChar :: CanParse m => m Char
nameChar = charByType LetterChar <|> charByType DigitChar <|> charByType MiscChar <|> charByType QuestChar
nameNonOpChar :: CanParse m => m Char
nameNonOpChar = charByType LetterChar <|> charByType DigitChar
opChar :: CanParse m => m Char
opChar = charByType MiscChar

nameStickyChar :: CanParse m => m Char
nameStickyChar = nameChar <|> MP.char '.'

natLiteralPrecise :: (CanParse m, Num n, Read n) => m n
natLiteralPrecise = do
  --string <- some $ charByType DigitChar
  string <- MP.label "natural number" $ MP.try ((some $ charByType DigitChar) <* MP.notFollowedBy nameChar)
  return $ (read string)
natLiteralNonSticky :: (CanParse m, Num n, Read n) => m n
natLiteralNonSticky = nonStickyLexeme $ natLiteralPrecise

nonStickyLexeme :: CanParse m => m a -> m a
nonStickyLexeme p = (lexeme . MP.try) (p <* MP.notFollowedBy nameStickyChar)

keyword :: CanParse m => String -> m ()
keyword w = nonStickyLexeme (void $ MP.string w)
--keyword w = (lexeme . MP.try) (MP.string w *> MP.notFollowedBy nameStickyChar)

wordPrecise :: CanParse m => m String
wordPrecise = MP.label "some word" $ MP.try $ do
  string <- many nameChar
  if string `elem` keywords
    then fail $ "Keyword " ++ show string ++ " cannot be an identifier."
    else if (and $ map isDigit string)
      then fail $ "Number " ++ show string ++ " cannot be an identifier."
      else return string
unqWord :: CanParse m => m String
unqWord = nonStickyLexeme wordPrecise
qWord :: CanParse m => m (Raw.Qualified String)
qWord = qualified unqWord
           
goal :: CanParse m => m String
goal = questionMarkPrecise *> unqWord

-------------------------------------------------------------

nonOpPrecise :: CanParse m => m String
nonOpPrecise = MP.label "non-operator identifier" $ MP.try $ do
  letter <- nameNonOpChar
  letters <- many nameChar
  let string = letter : letters
  if string `elem` keywords
    then fail $ "Keyword " ++ show string ++ " cannot be an identifier."
    else if (and $ map isDigit string)
      then fail $ "Number " ++ show string ++ " cannot be an identifier."
      else return string

opPrecise :: CanParse m => m String
opPrecise = MP.label "operator identifier" $ MP.try $ do
  letter <- opChar
  letters <- many nameChar
  let string = letter : letters
  if string `elem` keywords
    then fail $ "Keyword " ++ show string ++ " cannot be an identifier."
    else if (and $ map isDigit string)
      then fail $ "Number " ++ show string ++ " cannot be an identifier."
      else return $ string

qualified :: CanParse m => m a -> m (Raw.Qualified a)
qualified p = lexeme $ do
  modules <- manyTry $ (wordPrecise <* dotPrecise)
  thing <- p
  return $ Raw.Qualified modules thing

unqNonOp :: CanParse m => m Raw.Name
unqNonOp = MP.label "unqualified non-operator name" $ nonStickyLexeme $ Raw.Name Raw.NonOp <$> nonOpPrecise

qNonOp :: CanParse m => m Raw.QName
qNonOp = MP.label "qualified non-operator name" $ qualified unqNonOp

unqOp :: CanParse m => m Raw.Name
unqOp = MP.label "unqualified operator" $ nonStickyLexeme $ Raw.Name Raw.Op <$> opPrecise

qOp :: CanParse m => m Raw.QName
qOp = MP.label "qualified operator" $ qualified unqOp

unqName :: CanParse m => m Raw.Name
unqName = unqNonOp <|> parens unqOp

qName :: CanParse m => m Raw.QName
qName = qNonOp <|> parens qOp

-- expression subparsers -----------------------------------

expr3 :: CanParse m => m Raw.Expr3
expr3 = MP.label "atomic expression" $
  (Raw.ExprParens <$> parens expr) <|>
  (Raw.ExprImplicit <$ loneUnderscore) <?|>
  (Raw.ExprQName <$> qName) <?|>
  (Raw.ExprNatLiteral <$> natLiteralNonSticky) <?|>
  (Raw.ExprGoal <$> goal)

argNext :: CanParse m => m Raw.Eliminator
argNext = Raw.ElimArg Raw.ArgSpecNext <$> (dotPrecise *> accols expr)
argExplicit :: CanParse m => m Raw.Eliminator
argExplicit = Raw.ElimArg Raw.ArgSpecExplicit . Raw.expr3to1smart <$> expr3
argNamed :: CanParse m => m Raw.Eliminator
argNamed = (dotPrecise *>) $ accols $ do
  aName <- unqName
  keyword "="
  aValue <- expr
  return $ Raw.ElimArg (Raw.ArgSpecNamed aName) aValue

projectorNamed :: CanParse m => m Raw.ProjSpec
projectorNamed = Raw.ProjSpecNamed <$> (dotPrecise *> unqName)
projectorNumbered :: CanParse m => m Raw.ProjSpec
projectorNumbered = Raw.ProjSpecNumbered <$> (dotPrecise *> natLiteralNonSticky)
projectorTail :: CanParse m => m Raw.ProjSpec
projectorTail = Raw.ProjSpecTail <$> (dotPrecise *> dotPrecise *> natLiteralNonSticky)

eliminator :: CanParse m => m Raw.Eliminator
eliminator = MP.label "eliminator" $
  argExplicit <|> argNext <?|> argNamed <?|>
  (Raw.ElimProj <$> (projectorNamed <?|> projectorNumbered <?|> projectorTail))
opEliminator :: CanParse m => m Raw.Eliminator
opEliminator = MP.label "operator eliminator" $ argNext <?|> argNamed
annotEliminator :: CanParse m => m Raw.Eliminator
annotEliminator = MP.label "annotation eliminator" $ argExplicit <|> argNext <?|> argNamed

{-
argEndNext :: CanParse m => m Raw.Eliminator
argEndNext = Raw.ElimEnd Raw.ArgSpecNext <$ loneDots
argEndNamed :: CanParse m => m Raw.Eliminator
argEndNamed = (dotPrecise *>) $ accols $ do
  aName <- unqName
  keyword "="
  loneDots
  return $ Raw.ElimEnd $ Raw.ArgSpecNamed aName
-}
eliminatorEnd :: CanParse m => m Raw.Eliminator
eliminatorEnd = Raw.ElimDots <$ loneDots
--eliminatorEnd = MP.label "end-of-elimination marker" $ argEndNext <?|> argEndNamed

eliminators :: CanParse m => m [Raw.Eliminator]
eliminators = MP.label "eliminators" $
  (++) <$> manyTry eliminator <*> (fromMaybe [] <$> optionalTry ((: []) <$> eliminatorEnd))
opEliminators :: CanParse m => m [Raw.Eliminator]
opEliminators = MP.label "operator eliminators" $ manyTry opEliminator
annotEliminators :: CanParse m => m [Raw.Eliminator]
annotEliminators = MP.label "annotation eliminators" $ manyTry annotEliminator

elimination :: CanParse m => m Raw.Elimination
elimination = Raw.Elimination <$> expr3 <*> eliminators

expr2 :: CanParse m => m Raw.Expr2
expr2 = MP.label "operator-free expression" $ Raw.ExprElimination <$> elimination

operand :: CanParse m => m Raw.Operand
operand = (Raw.OperandTelescope <$> telescopeSome) <?|> (Raw.OperandExpr <$> expr2)

operatorHead :: CanParse m => m Raw.Expr3
operatorHead = (ticks $ Raw.ExprParens <$> expr) <|> (Raw.ExprQName <$> qOp)
operator :: CanParse m => m Raw.Elimination
operator = MP.label "operator with eliminations" $ Raw.Elimination <$> operatorHead <*> opEliminators

expr :: CanParse m => m Raw.Expr
expr = MP.label "expression" $ do
  anOperand <- operand
  rest <- optional $ do
    anOperator <- operator
    maybeExpr <- optional expr
    return (anOperator, maybeExpr)
  return $ Raw.ExprOps anOperand rest

{-
atom :: CanParse m => m Raw.Atom
atom = (Raw.AtomQName <$> qIdentifier)
  <|> (Raw.AtomParens <$> parens expr)
  <|> (Raw.AtomDot <$ dot)
  <|> (Raw.AtomSegment <$> segment)
  <|> (Raw.AtomNatLiteral <$> natLiteral)

expr :: CanParse m => m Raw.Expr
expr = Raw.Expr <$> some atom
-}

-- high-level subparsers -----------------------------------

-- annotations - old

{-
atomicAnnotation :: CanParse m => m Raw.Annotation
atomicAnnotation = (\qword -> Raw.Annotation qword []) <$> qWord

compoundAnnotation :: CanParse m => m Raw.Annotation
compoundAnnotation = brackets $ do
  qword <- qWord
  content <- annotEliminators
  return $ Raw.Annotation qword content

annotation :: CanParse m => m Raw.Annotation
annotation = MP.label "annotation" $ atomicAnnotation <|> compoundAnnotation

annotationClause :: CanParse m => m [Raw.Annotation]
annotationClause = MP.label "annotation clause" $ MP.try $ many annotation <* pipe

entryAnnotation :: CanParse m => m Raw.Annotation
entryAnnotation = compoundAnnotation
-}

-- annotations - new

annotation :: CanParse m => m Raw.Annotation
annotation = MP.label "annotation" $ do
  annotName <- qWord
  annotArg <- optional expr
  return $ Raw.Annotation annotName annotArg

segmentAnnotations :: CanParse m => m [Raw.Annotation]
segmentAnnotations = manyTry $ annotation <* pipe

entryAnnotations :: CanParse m => m [Raw.Annotation]
entryAnnotations = brackets $ manySep pipe annotation

-- telescopes

segment :: CanParse m => m Raw.Segment
segment = MP.label "telescope segment" $ accols $ do
      annots <- segmentAnnotations --fromMaybe [] <$> optionalTry annotationClause
      names <- Raw.DeclNamesSegment <$> some ((Just <$> unqName) <|> (Nothing <$ loneUnderscore))
      --context <- telescopeMany
      maybeType <- optional $ keyword ":" *> expr
      return $ Raw.Segment $ Raw.Declaration {
        Raw.decl'annotations = annots,
        Raw.decl'names = names,
        Raw.decl'telescope = Raw.Telescope [],
        Raw.decl'content = fromMaybe Raw.DeclContentEmpty $ Raw.DeclContent <$> maybeType
      }

telescopeMany :: CanParse m => m Raw.Telescope
telescopeMany = MP.label "telescope (possibly empty)" $ Raw.Telescope <$> many segment

telescopeSome :: CanParse m => m Raw.Telescope
telescopeSome = MP.label "telescope (non-empty)" $ Raw.Telescope <$> some segment

lhs :: CanParse m => Raw.EntryHeader declSort -> m (Raw.Declaration declSort)
lhs header = MP.label "LHS" $ do
  annots <- entryAnnotations --many entryAnnotation
  name <- case header of
    Raw.HeaderToplevelModule -> do
      qname <- qName
      qstring <- sequenceA $ (<$> qname) $ \ name -> case name of
        Raw.Name Raw.NonOp str' -> return str'
        _ -> fail $ "Expected non-operator name: " ++ Raw.unparse qname
      return $ Raw.DeclNamesToplevelModule qstring
    Raw.HeaderModule -> do
      qname <- qName
      str <- case qname of
        Raw.Qualified [] (Raw.Name Raw.NonOp str') -> return str'
        _ -> fail $ "Expected unqualified non-operator name: " ++ Raw.unparse qname
      return $ Raw.DeclNamesModule str
    Raw.HeaderVal -> do
      qname <- qName
      name <- case qname of
        Raw.Qualified [] name' -> return name'
        _ -> fail $ "Expected unqualified name: " ++ Raw.unparse qname
      return $ Raw.DeclNamesVal name
    header -> fail $ "Not supported yet: " ++ Raw.headerKeyword header
  context <- telescopeMany
  maybeType <- optional $ do
    keyword ":"
    expr
  declContentType <- case maybeType of
    Nothing -> return $ Raw.DeclContentEmpty
    Just ty -> case header of
      Raw.HeaderModule -> fail $ "Did not expect a type here: " ++ Raw.unparse ty
      Raw.HeaderToplevelModule -> fail $ "Did not expect a type here: " ++ Raw.unparse ty
      Raw.HeaderVal -> return $ Raw.DeclContent ty
      _ -> fail $ "Not supported yet: " ++ Raw.headerKeyword header
  return $ Raw.Declaration {
    Raw.decl'annotations = annots,
    Raw.decl'names = name,
    Raw.decl'telescope = context,
    Raw.decl'content = declContentType
    }

moduleRHS :: CanParse m => m (Raw.RHS (Raw.DeclSortModule b))
moduleRHS = MP.label "module RHS" $
  Raw.RHSModule <$> (keyword "where" *> (accols $ many entry))
  {-do
  keyword "module"
  entries <- accols $ many entry
  return $ Raw.RHSModule entries-}

valRHS :: CanParse m => m (Raw.RHS Raw.DeclSortVal)
valRHS = Raw.RHSVal <$> (keyword "=" *> expr) 

rhs :: CanParse m => Raw.EntryHeader declSort -> m (Raw.RHS declSort)
rhs Raw.HeaderToplevelModule = moduleRHS
rhs Raw.HeaderModule = moduleRHS
rhs Raw.HeaderVal = valRHS
rhs Raw.HeaderData = fail "Not supported yet: data"
rhs Raw.HeaderCodata = fail "Not supported yet : codata"
rhs Raw.HeaderResolution = fail "Not supported yet : resolution" --return Raw.RHSResolution

entryHeader :: CanParse m => m Raw.AnyEntryHeader
entryHeader =
    (Raw.AnyEntryHeader Raw.HeaderModule <$ keyword "module")
    <|> (Raw.AnyEntryHeader Raw.HeaderVal <$ keyword "val")
    <|> (Raw.AnyEntryHeader Raw.HeaderData <$ keyword "data")
    <|> (Raw.AnyEntryHeader Raw.HeaderCodata <$ keyword "codata")
    <|> (Raw.AnyEntryHeader Raw.HeaderResolution <$ keyword "resolution")

{-
modul :: CanParse m => m Raw.Module
modul = do
  anEntry <- entry
  case anEntry of
    Raw.EntryModule aModule -> return aModule
    _ -> fail "Expected a module" -- TODO
-}

entry :: CanParse m => m Raw.AnyEntry
entry = MP.label "entry" $ do
  Raw.AnyEntryHeader header <- entryHeader
  anLHS <- lhs header
  anRHS <- rhs header
  return $ Raw.AnyEntry $ Raw.EntryLR header anLHS anRHS

toplevelEntry :: CanParse m => m Raw.AnyEntry
toplevelEntry = MP.label "entry" $ do
  keyword "module"
  anLHS <- lhs Raw.HeaderToplevelModule
  anRHS <- rhs Raw.HeaderToplevelModule
  return $ Raw.AnyEntry $ Raw.EntryLR Raw.HeaderToplevelModule anLHS anRHS

file :: CanParse m => m Raw.File
file = MP.between manySpace MP.eof $ do
  Raw.AnyEntry themodule <- toplevelEntry
  case Raw.entry'header themodule of
    Raw.HeaderToplevelModule -> return $ Raw.File themodule
    _ -> fail $ "Top level entry should be a module : " ++ Raw.unparse themodule
