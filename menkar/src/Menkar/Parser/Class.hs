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

