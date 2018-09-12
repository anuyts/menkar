{-# LANGUAGE FlexibleContexts, FlexibleInstances, ApplicativeDo #-}

module Menkar.Parser where

import qualified Text.Megaparsec as MP
import qualified Text.Megaparsec.Char as MP
import qualified Text.Megaparsec.Expr as MP
import qualified Menkar.Raw as Raw
import qualified Text.Megaparsec.Char.Lexer as MPL
import Control.Monad.Identity
import Control.Applicative
import Data.Char
import Data.Number.Nat
import Data.Maybe
--import Data.Ord

-- Testing -------------------------------------------------

type TestParser = MP.Parsec ParseError String
instance CanParse (MP.ParsecT ParseError String Identity)

testparse :: String -> IO (Either (MP.ParseError Char ParseError) Raw.File)
testparse filename = do
  let path = "Menkar/code-examples/" ++ filename
  code <- readFile path
  return $ MP.parse file path code

quickParse :: MP.Parsec ParseError String a -> String -> a
quickParse parser code = case MP.parse parser "quick" code of
  Left e -> error $ show e
  Right a -> a

-- ParseError ----------------------------------------------

data ParseError
instance Eq ParseError where
  e == e' = True
instance Ord ParseError where
  compare e e' = EQ
instance Show ParseError where
  show e = "ERROR"

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

infixl 3 <?|>

-- characters ----------------------------------------------

data CharType =
  SpaceChar | LetterChar | DigitChar | LooseChar | MiscChar | OpenChar | CloseChar
  deriving (Show, Eq)

looseChars :: [Char]
looseChars = "|_`."

describeCharType :: CharType -> String
describeCharType ct = case ct of
  SpaceChar -> "whitespace character (unicode)"
  LetterChar -> "letter character (unicode)"
  DigitChar -> "digit"
  LooseChar -> "one of " ++ looseChars
  MiscChar -> "miscellaneous unicode character"
  OpenChar -> "opening delimiter (unicode)"
  CloseChar -> "closing delimiter (unicode)"

charType :: Char -> CharType
charType c
  | isSpace c = SpaceChar
  | isDigit c = DigitChar
  | isLetter c = LetterChar
  | elem c looseChars = LooseChar
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

{-| 'lexeme p' consumes 'p', then 'manySpace'. -}
lexeme :: CanParse m => m a -> m a
lexeme = MPL.lexeme manySpace
{-| 'loneLexeme p' consumes 'p', then 'someSpace'. -}
loneLexeme :: CanParse m => m a -> m a
loneLexeme = MPL.lexeme someSpace

{-| Consumes and returns the specified string.
    DO NOT USE THIS FOR KEYWORDS, lest "ifbla" will be parsed as "if bla".
    Use for "|", ",". -}
symbol :: CanParse m => String -> m String
symbol = lexeme . MP.string

pipe :: CanParse m => m ()
pipe = void $ symbol "|"

tickPrecise :: CanParse m => m ()
tickPrecise = void $ MP.string "`"
underscorePrecise :: CanParse m => m ()
underscorePrecise = void $ MP.string "_"
dotPrecise :: CanParse m => m ()
dotPrecise = void $ MP.string "."

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

charByType :: CanParse m => CharType -> m Char
charByType ct = MP.label (describeCharType ct) $ MP.satisfy (\ c -> charType c == ct)

nameChar :: CanParse m => m Char
nameChar = charByType LetterChar <|> charByType DigitChar <|> charByType MiscChar
nameNonOpChar :: CanParse m => m Char
nameNonOpChar = charByType LetterChar <|> charByType DigitChar
opChar :: CanParse m => m Char
opChar = charByType MiscChar

nameStickyChar :: CanParse m => m Char
nameStickyChar = nameChar <|> MP.char '.'

natLiteralPrecise :: CanParse m => m Nat
natLiteralPrecise = do
  --string <- some $ charByType DigitChar
  string <- MP.label "natural number" $ MP.try ((some $ charByType DigitChar) <* MP.notFollowedBy nameChar)
  return $ (read string :: Nat)
natLiteralNonSticky :: CanParse m => m Nat
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

--formerly called identifierString
nameNonOpPrecise :: CanParse m => m String
nameNonOpPrecise = MP.label "non-operator identifier" $ MP.try $ do
  letter <- nameNonOpChar
  letters <- many nameChar
  let string = letter : letters
  if string `elem` keywords
    then fail $ "Keyword " ++ show string ++ " cannot be an identifier."
    else if (and $ map isDigit string)
      then fail $ "Number " ++ show string ++ " cannot be an identifier."
      else return string

nameNonOpNonSticky :: CanParse m => m String
nameNonOpNonSticky = nonStickyLexeme nameNonOpPrecise

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

nameOpPrecise :: CanParse m => m String
nameOpPrecise = underscorePrecise *> opPrecise

namePrecise :: CanParse m => m Raw.Name
namePrecise = (Raw.Name Raw.NonOp <$> nameNonOpPrecise) <|> (Raw.Name Raw.Op <$> nameOpPrecise)

unqName :: CanParse m => m Raw.Name
unqName = MP.label "unqualified identifier" $ nonStickyLexeme namePrecise
  {-
  lexeme $ namePrecise <* (MP.notFollowedBy nameStickyChar <|> fail msg)
  where
    msg = "You have either neglected to leave a space after this identifier, or you have used a" ++
      " qualified identifier where an unqualified one was expected."
  -}

qualified :: CanParse m => m a -> m (Raw.Qualified a)
qualified p = lexeme $ do
  modules <- manyTry $ (nameNonOpPrecise <* dotPrecise)
  thing <- p
  return $ Raw.Qualified modules thing

qName :: CanParse m => m Raw.QName
qName = MP.label "qualified identifier" $ qualified unqName

tickedQName :: CanParse m => m Raw.QName
tickedQName = tickPrecise *> qName

unqOp :: CanParse m => m Raw.Name
unqOp = MP.label "unqualified operator" $ nonStickyLexeme $ Raw.Name Raw.Op <$> opPrecise
  {-
  lexeme $ Raw.Name Raw.Op <$> opPrecise <* (MP.notFollowedBy nameStickyChar <|> fail msg)
  where
    msg = "You have neglected to leave a space after this operator."
  -}

--qOp :: CanParse m => m Raw.QName
--qOp = MP.label "qualified operator" $ tickedQName <|> (Raw.Qualified [] <$> unqOp)

{-
qIdentifier :: CanParse m => m Raw.QName
qIdentifier = MP.label "qualified identifier" $ lexeme $ do
  head <- identifierString
  tail <- many $ do
    MP.char '.'
    identifierString <|> fail "Another identifier is expected after '.', with no space in between."
  return $ Raw.QName (head : tail)
-}

{-
haskellCharLiteral :: CanParse m => m String
haskellCharLiteral = MP.label "Haskell character literal" $ do
  "'" <- MP.string "'"
  content <- many $ (MP.label "any character other than (') or (\\)" $
                      return <$> MP.satisfy (\ c . not $ c `elem` ['\'', '\\']))
                    <|> MP.string "\\'"
                    <|> (MP.string "\\" <* MP.notFollowedBy (MP.String "\'"))
  "'" <- MP.string "'"
  return $ "'" ++ concat content ++ "'"
-}

{-
{-| Parses any rubbish, including what would otherwise be a comment,
    until a parenthesis closes that was never opened. Parentheses need not match.
    This parser is unaware of quotes. Don't use strings containing parentheses in Menkar
    pseudocode. -}
haskellCode :: CanParse m => m String
haskellCode = MP.label "Haskell code" $ fmap concat $ many $
  ((\ c -> [c]) <$> MP.satisfy (\ c -> not $ charType c `elem` [OpenChar, CloseChar]))
  <|> do
        openChar <- MP.satisfy (\ c -> charType c == OpenChar)
        contents <- haskellCode
        closeChar <- MP.satisfy (\ c -> charType c == CloseChar)
        return $ [openChar] ++ contents ++ [closeChar]

haskellCodeBracketed :: CanParse m => m String
haskellCodeBracketed = lexeme $
  MP.between (MP.string "[") (MP.string "]") haskellCode
-}

{-
optionalEntrySep :: CanParse m => m ()
optionalEntrySep = void (symbol ",") <|> return ()

requiredEntrySep :: CanParse m => m ()
requiredEntrySep = void $ symbol "," <|> MP.lookAhead (symbol "}")
-}

-- expression subparsers -----------------------------------

expr3 :: CanParse m => m Raw.Expr3
expr3 = MP.label "atomic expression" $
  (Raw.ExprParens <$> parens expr) <|>
  (Raw.ExprImplicit <$ loneUnderscore) <?|>
  (Raw.ExprQName <$> qName) <?|>
  (Raw.ExprNatLiteral <$> natLiteralNonSticky)

argNext :: CanParse m => m Raw.Eliminator
argNext = Raw.ElimArg Raw.ArgSpecNext <$> (dotPrecise *> accols expr)
argExplicit :: CanParse m => m Raw.Eliminator
argExplicit = Raw.ElimArg Raw.ArgSpecExplicit . Raw.expr3to1smart <$> expr3
argNamed :: CanParse m => m Raw.Eliminator
argNamed = (dotPrecise *>) $ accols $ do
  aName <- nameNonOpNonSticky
  keyword "="
  aValue <- expr
  return $ Raw.ElimArg (Raw.ArgSpecNamed aName) aValue

projectorNamed :: CanParse m => m Raw.ProjSpec
projectorNamed = Raw.ProjSpecNamed <$> (dotPrecise *> nameNonOpNonSticky)
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

argEndNext :: CanParse m => m Raw.Eliminator
argEndNext = Raw.ElimEnd Raw.ArgSpecNext <$ loneDots
argEndNamed :: CanParse m => m Raw.Eliminator
argEndNamed = (dotPrecise *>) $ accols $ do
  aName <- nameNonOpNonSticky
  keyword "="
  loneDots
  return $ Raw.ElimEnd $ Raw.ArgSpecNamed aName
eliminatorEnd :: CanParse m => m Raw.Eliminator
eliminatorEnd = MP.label "end-of-elimination marker" $ argEndNext <?|> argEndNamed

eliminators :: CanParse m => m [Raw.Eliminator]
eliminators = MP.label "eliminators" $
  (++) <$> manyTry eliminator <*> (fromMaybe [] <$> optionalTry ((: []) <$> eliminatorEnd))
opEliminators :: CanParse m => m [Raw.Eliminator]
opEliminators = MP.label "operator eliminators" $ manyTry opEliminator

elimination :: CanParse m => m Raw.Elimination
elimination = Raw.Elimination <$> expr3 <*> eliminators

expr2 :: CanParse m => m Raw.Expr2
expr2 = MP.label "operator-free expression" $ Raw.ExprElimination <$> elimination

operand :: CanParse m => m Raw.Operand
operand = (Raw.OperandTelescope <$> telescopeSome) <?|> (Raw.OperandExpr <$> expr2)

operatorHead :: CanParse m => m Raw.Expr3
operatorHead = (tickPrecise *> expr3) <|> (Raw.ExprQName . Raw.Qualified [] <$> unqOp)
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

-- annotations

--haskellAnnotation :: CanParse m => m Raw.Annotation
--haskellAnnotation = Raw.AnnotationHaskell <$> haskellCodeBracketed

atomicAnnotation :: CanParse m => m Raw.Annotation
atomicAnnotation = (\qword -> Raw.Annotation qword []) <$> qWord

compoundAnnotation :: CanParse m => m Raw.Annotation
compoundAnnotation = brackets $ do
  qword <- qWord
  content <- many expr3
  return $ Raw.Annotation qword content

annotation :: CanParse m => m Raw.Annotation
annotation = MP.label "annotation" $ atomicAnnotation <|> compoundAnnotation

annotationClause :: CanParse m => m [Raw.Annotation]
annotationClause = MP.label "annotation clause" $ MP.try $ many annotation <* pipe

entryAnnotation :: CanParse m => m Raw.Annotation
entryAnnotation = compoundAnnotation

-- telescopes

--segmentNamesAndColon :: CanParse m => m Raw.LHSNames
--segmentNamesAndColon = Raw.SomeNamesForTelescope <$> some unqName <* keyword ":"

--segmentConstraintColon :: CanParse m => m Raw.LHSNames
--segmentConstraintColon = Raw.NoNameForConstraint <$ keyword "-:"

constraint :: CanParse m => m Raw.LHS
constraint = accols $ do
      annots <- fromMaybe [] <$> optionalTry annotationClause
      keyword "-:"
      typ <- expr
      return $ Raw.LHS {
        Raw.annotationsLHS = annots,
        Raw.namesLHS = Raw.NoNameForConstraint,
        Raw.contextLHS = Raw.Telescope [],
        Raw.typeLHS = Just typ
      }

argument :: CanParse m => m Raw.LHS 
argument = accols $ do
      annots <- fromMaybe [] <$> optionalTry annotationClause
      --names <- segmentNamesAndColon <|> segmentConstraintColon
      names <- Raw.SomeNamesForTelescope <$> some ((Just <$> unqName) <|> (Nothing <$ loneUnderscore))
      context <- telescopeMany
      maybeType <- optional $ keyword ":" *> expr
      return $ Raw.LHS {
        Raw.annotationsLHS = annots,
        Raw.namesLHS = names,
        Raw.contextLHS = context,
        Raw.typeLHS = maybeType
      }

segment :: CanParse m => m Raw.Segment
segment = MP.label "telescope segment" $ Raw.Segment <$> (argument <?|> constraint)

telescopeMany :: CanParse m => m Raw.Telescope
telescopeMany = MP.label "telescope (possibly empty)" $ Raw.Telescope <$> many segment

telescopeSome :: CanParse m => m Raw.Telescope
telescopeSome = MP.label "telescope (non-empty)" $ Raw.Telescope <$> some segment

lhs :: CanParse m => m Raw.LHS
lhs = MP.label "LHS" $ do
  annots <- many entryAnnotation
  name <- Raw.QNameForEntry <$> qName
  context <- telescopeMany
  maybeType <- optional $ do
    keyword ":"
    expr
  return $ Raw.LHS {
    Raw.annotationsLHS = annots,
    Raw.namesLHS = name,
    Raw.contextLHS = context,
    Raw.typeLHS = maybeType
    }

moduleRHS :: CanParse m => m Raw.RHS
moduleRHS = MP.label "module RHS" $
  Raw.RHSModule <$> (keyword "where" *> (accols $ many entry))
  {-do
  keyword "module"
  entries <- accols $ many entry
  return $ Raw.RHSModule entries-}

valRHS :: CanParse m => m Raw.RHS
valRHS = Raw.RHSVal <$> (keyword "=" *> expr) 

rhs :: CanParse m => Raw.EntryHeader -> m Raw.RHS
rhs Raw.HeaderModule = moduleRHS
rhs Raw.HeaderVal = valRHS
rhs Raw.HeaderData = fail "Not supported yet: data"
rhs Raw.HeaderCodata = fail "Not supported yet : codata"
rhs Raw.HeaderResolution = fail "Not supported yet : resolution" --return Raw.RHSResolution

entryHeader :: CanParse m => m Raw.EntryHeader
entryHeader =
  (Raw.HeaderModule <$ keyword "module")
  <|> (Raw.HeaderVal <$ keyword "val")
  <|> (Raw.HeaderData <$ keyword "data")
  <|> (Raw.HeaderCodata <$ keyword "codata")
  <|> (Raw.HeaderResolution <$ keyword "resolution")

lrEntry :: CanParse m => m Raw.LREntry
lrEntry = MP.label "entry" $ do
  header <- entryHeader
  anLHS <- lhs
  anRHS <- rhs header
  return $ Raw.LREntry header anLHS anRHS

{-
modul :: CanParse m => m Raw.Module
modul = do
  anEntry <- entry
  case anEntry of
    Raw.EntryModule aModule -> return aModule
    _ -> fail "Expected a module" -- TODO
-}

entry :: CanParse m => m Raw.Entry
entry = (Raw.EntryLR <$> lrEntry)

file :: CanParse m => m Raw.File
file = MP.between manySpace MP.eof $ do
  themodule <- lrEntry
  return $ Raw.File themodule
