{-# LANGUAGE FlexibleContexts, FlexibleInstances #-}

module Menkar.Parser where

import qualified Text.Megaparsec as MP
import qualified Text.Megaparsec.Char as MP
import qualified Text.Megaparsec.Expr as MP
import qualified Menkar.Raw as Raw
import qualified Text.Megaparsec.Char.Lexer as MPL
import Control.Monad.Identity
--import Data.Ord

data ParseError
instance Eq ParseError where
  e == e' = True
instance Ord ParseError where
  compare e e' = EQ
instance Show ParseError where
  show e = "ERROR"

class (MP.MonadParsec ParseError String m) => CanParse m

type TestParser = MP.Parsec ParseError String
instance CanParse (MP.ParsecT ParseError String Identity)

manySpace :: CanParse m => m ()
manySpace = MPL.space MP.space1 lineCmnt blockCmnt
  where
    lineCmnt  = MPL.skipLineComment "//"
    blockCmnt = MPL.skipBlockComment "/*" "*/"

--parse :: MonadParser m => m Raw.Module
--parse = _
