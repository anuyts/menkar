module Menkar.Parser where

import qualified Text.Megaparsec as MP

type ParseError = Void

class (MP.MonadParsec ParseError String m) => MonadParser m


