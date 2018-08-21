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

-- characters ----------------------------------------------

data CharType =
  SpaceChar | LetterChar | DigitChar | LooseChar | MiscChar | OpenChar | CloseChar
  deriving (Show, Eq)

looseChars :: [Char]
looseChars = "|'`."

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
           --, "-:"    -- typing propositions
           , "="     -- assignment
           , "->"    -- function type
           , "><"    -- sigma type
           --, "Uni"   -- universe
           --, "?"     -- for Glue etc.
           , ">"    -- mapsto
           , "<"    -- mapsfrom
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
           ]

-- basic subparsers ----------------------------------------

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
natLiteral :: CanParse m => m Nat
natLiteral = lexeme $ natLiteralPrecise

keyword :: CanParse m => String -> m ()
keyword w = (lexeme . MP.try) (MP.string w *> MP.notFollowedBy nameStickyChar)

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

opPrecise :: CanParse m => m String
opPrecise = MP.label "operator identifier" $ MP.try $ do
  letter <- opChar
  letters <- many nameChar
  let string = letter : letters
  if string `elem` keywords
    then fail $ "Keyword " ++ show string ++ " cannot be an identifier."
    else if (and $ map isDigit string)
      then fail $ "Number " ++ show string ++ " cannot be an identifier."
      else return string

nameOpPrecise :: CanParse m => m String
nameOpPrecise = underscorePrecise *> opPrecise

namePrecise :: CanParse m => m Raw.Name
namePrecise = (Raw.Name Raw.NonOp <$> nameNonOpPrecise) <|> (Raw.Name Raw.Op <$> nameOpPrecise)

unqName :: CanParse m => m Raw.Name
unqName = MP.label "unqualified identifier" $
  lexeme $ namePrecise <* (MP.notFollowedBy nameStickyChar <|> fail msg)
  where
    msg = "You have either neglected to leave a space after this identifier, or you have used a" ++
      " qualified identifier where an unqualified one was expected."

qName :: CanParse m => m Raw.QName
qName = MP.label "qualified identifier" $ lexeme $ do
  modules <- many $ (nameNonOpPrecise <* dotPrecise)
  theQName <- unqName
  return $ Raw.QName modules theQName

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

expr :: CanParse m => m Raw.Expr
expr = _

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
atomicAnnotation = (\qname -> Raw.Annotation qname Nothing) <$> qIdentifier

compoundAnnotation :: CanParse m => m Raw.Annotation
compoundAnnotation = parens $ do
  qname <- qIdentifier
  content <- expr
  return $ Raw.Annotation qname (Just content)

annotation :: CanParse m => m Raw.Annotation
annotation = MP.label "annotation" $ atomicAnnotation <|> compoundAnnotation

annotationClause :: CanParse m => m [Raw.Annotation]
annotationClause = MP.label "annotation clause" $ MP.try $ many annotation <* pipe

entryAnnotation :: CanParse m => m Raw.Annotation
entryAnnotation = brackets $ do
  qname <- qIdentifier
  content <- optional expr
  return $ Raw.Annotation qname content

-- telescopes

segmentNamesAndColon :: CanParse m => m Raw.LHSNames
segmentNamesAndColon = Raw.SomeNamesForTelescope <$> some unqIdentifier <* keyword ":"

segmentConstraintColon :: CanParse m => m Raw.LHSNames
segmentConstraintColon = Raw.NoNameForConstraint <$ keyword "-:"

constraint :: CanParse m => m Raw.LHS
constraint = accols $ do
      annots <- fromMaybe [] <$> optional annotationClause
      keyword "-:"
      typ <- expr
      return $ Raw.LHS {
        Raw.annotationsLHS = annots,
        Raw.namesLHS = Raw.NoNameForConstraint,
        Raw.contextLHS = Raw.Telescope [],
        Raw.typeLHS = Just typ
      }

argument :: CanParse m => m Raw.LHS 
argument = MP.try $ accols $ do
      annots <- fromMaybe [] <$> optional annotationClause
      --names <- segmentNamesAndColon <|> segmentConstraintColon
      names <- Raw.SomeNamesForTelescope <$> some unqIdentifier
      context <- telescopeMany
      maybeType <- optional $ keyword ":" *> expr
      return $ Raw.LHS {
        Raw.annotationsLHS = annots,
        Raw.namesLHS = names,
        Raw.contextLHS = context,
        Raw.typeLHS = maybeType
      }

segment :: CanParse m => m Raw.Segment
segment = MP.label "telescope segment" $ Raw.Segment <$> (argument <|> constraint)

telescopeMany :: CanParse m => m Raw.Telescope
telescopeMany = MP.label "telescope (possibly empty)" $ Raw.Telescope <$> many segment

telescopeSome :: CanParse m => m Raw.Telescope
telescopeSome = MP.label "telescope (non-empty)" $ Raw.Telescope <$> some segment

lhs :: CanParse m => m Raw.LHS
lhs = MP.label "LHS" $ do
  annots <- many entryAnnotation
  name <- Raw.QNameForEntry <$> qIdentifier
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
rhs Raw.HeaderResolution = return Raw.RHSResolution

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
