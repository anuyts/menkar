{-# LANGUAGE FlexibleContexts, FlexibleInstances #-}

module Menkar.Parser where

import qualified Text.Megaparsec as MP
import qualified Text.Megaparsec.Char as MP
import qualified Text.Megaparsec.Expr as MP
import qualified Menkar.Raw as Raw
import qualified Text.Megaparsec.Char.Lexer as MPL
import Control.Monad.Identity
import Data.Char
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

-- characters ----------------------------------------------

data CharType =
  SpaceChar | LetterChar | DigitChar | UnderscoreChar | OpChar | OpenChar | CloseChar
  deriving (Show, Eq)

charType :: Char -> CharType
charType c
  | isSpace c = SpaceChar
  | isDigit c = DigitChar
  | isLetter c = LetterChar
  | c == '_' = UnderscoreChar
  | otherwise = case generalCategory c of
      OpenPunctuation -> OpenChar
      ClosePunctuation -> CloseChar
      _ -> OpChar

-- subparsers ----------------------------------------------

{-| Consumes zero or more whitespace characters, line or block comments -}
manySpace :: CanParse m => m ()
manySpace = MPL.space MP.space1 lineCmnt blockCmnt
  where
    lineCmnt  = MPL.skipLineComment "//"
    blockCmnt = MPL.skipBlockComment "/*" "*/"

{-| 'lexeme p' consumes 'p', then 'manySpace'. -}
lexeme :: CanParse m => m a -> m a
lexeme = MPL.lexeme manySpace

{-| Cconsumes and returns the specified string.
    DO NOT USE THIS FOR RESERVED WORDS, lest "ifbla" will be parsed as "if bla". -}
symbol :: CanParse m => String -> m String
symbol = MPL.symbol manySpace

parens :: CanParse m => m a -> m a
parens = MP.between (symbol "(") (symbol ")")

accols :: CanParse m => m a -> m a
accols = MP.between (symbol "{") (symbol "}")

--parse :: MonadParser m => m Raw.Module
--parse = _
