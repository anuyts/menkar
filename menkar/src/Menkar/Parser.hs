{-# LANGUAGE FlexibleContexts, FlexibleInstances #-}

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
--import Data.Ord

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

type TestParser = MP.Parsec ParseError String
instance CanParse (MP.ParsecT ParseError String Identity)

(<?>) :: CanParse m => m a -> String -> m a
(<?>) = (MP.<?>)

-- characters ----------------------------------------------

data CharType =
  SpaceChar | LetterChar | DigitChar | LooseChar | MiscChar | OpenChar | CloseChar
  deriving (Show, Eq)

describeCharType :: CharType -> String
describeCharType ct = case ct of
  SpaceChar -> "whitespace character (unicode)"
  LetterChar -> "letter character (unicode)"
  DigitChar -> "digit"
  LooseChar -> "one of '|', ',' and '.'"
  MiscChar -> "miscellaneous unicode character"
  OpenChar -> "opening delimiter (unicode)"
  CloseChar -> "closing delimiter (unicode)"

charType :: Char -> CharType
charType c
  | isSpace c = SpaceChar
  | isDigit c = DigitChar
  | isLetter c = LetterChar
  | elem c ['|', ',', '.'] = LooseChar
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
keywords = [ "_"     -- omission / implicit term
           , "__"    -- instance term
           , ":"     -- typing
           , "-:"    -- typing propositions
           , "="     -- assignment
           , "->"    -- function type
           , "><"    -- sigma type
           , "Uni"   -- universe
           , ">>"    -- mapsto
           , "?"     -- for Glue etc.
           , "module"
           , "data"
           , "codata"
           , "syntax"
           , "import"
           , "open"
           ]

-- subparsers ----------------------------------------------

{-| Consumes zero or more whitespace characters, line or block comments -}
manySpace :: CanParse m => m ()
manySpace = MPL.space MP.space1 lineCmnt blockCmnt
  where
    lineCmnt  = MPL.skipLineComment "//"
    blockCmnt = MPL.skipBlockCommentNested "/*" "*/"

{-| 'lexeme p' consumes 'p', then 'manySpace'. -}
lexeme :: CanParse m => m a -> m a
lexeme = MPL.lexeme manySpace

{-| Cconsumes and returns the specified string.
    DO NOT USE THIS FOR KEYWORDS, lest "ifbla" will be parsed as "if bla". -}
symbol :: CanParse m => String -> m String
symbol = MPL.symbol manySpace

parens :: CanParse m => m a -> m a
parens = MP.between (symbol "(") (symbol ")")

accols :: CanParse m => m a -> m a
accols = MP.between (symbol "{") (symbol "}")

charByType :: CanParse m => CharType -> m Char
charByType ct = MP.satisfy (\ c -> charType c == ct) <?> describeCharType ct

nameChar :: CanParse m => m Char
nameChar = charByType LetterChar <|> charByType DigitChar <|> charByType MiscChar

nameStickyChar :: CanParse m => m Char
nameStickyChar = nameChar <|> MP.char '.'

natural :: CanParse m => m Nat
natural = do
  --string <- some $ charByType DigitChar
  string <- (lexeme . MP.try) ((some $ charByType DigitChar) <* MP.notFollowedBy nameChar)
  return $ (read string :: Nat)

keyword :: CanParse m => String -> m ()
keyword w = (lexeme . MP.try) (MP.string w *> MP.notFollowedBy nameStickyChar)

identifierString :: CanParse m => m String
identifierString = MP.label "identifier" $ MP.try $ do
  string <- some nameChar
  if string `elem` keywords
    then fail $ "Keyword " ++ show string ++ " cannot be an identifier."
    else if (and $ map isDigit string)
      then fail $ "Number " ++ show string ++ " cannot be an identifier."
      else return string

unqIdentifier :: CanParse m => m String
unqIdentifier = MP.label "unqualified identifier" $
  lexeme $ identifierString <* (MP.notFollowedBy nameStickyChar <|> fail msg)
  where
    msg = "You have either neglected to leave a space after this identifier, or you have used a" ++
      " qualified identifier where an unqualified one was expected."

qIdentifier :: CanParse m => m [String]
qIdentifier = MP.label "qualified identifier" $ lexeme $ do
  head <- identifierString
  tail <- many $ do
    MP.char '.'
    identifierString <|> fail "Another identifier is expected after '.', with no space in between."
  return $ head : tail

--parse :: MonadParser m => m Raw.Module
--parse = _
