module Menkar.Parser.Class where

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

