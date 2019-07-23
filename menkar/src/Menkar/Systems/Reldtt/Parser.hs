module Menkar.Systems.Reldtt.Parser where

import Menkar.Systems.Reldtt.Basic
import qualified Menkar.Systems.Reldtt.Raw as Raw
import qualified Menkar.Systems.Reldtt.PrettyPrint.Raw as Raw
import Menkar.System.Basic
import qualified Menkar.System.Raw as Raw
import Menkar.Parser

import Control.Applicative

degree :: CanParse m => m KnownDeg
degree =
  KnownDegEq <$ keyword "="
  <|> KnownDeg <$> natLiteralNonSticky
  <|> KnownDegTop <$ keyword "T"

modtySnout :: CanParse m => m ModtySnout
modtySnout = do
  kdegs <- many degree
  symbol ":"
  idom <- natLiteralNonSticky
  symbol "->"
  icod <- natLiteralNonSticky
  return $ ModtySnout idom icod (reverse kdegs)

modtyTailAspect :: CanParse m => m Raw.ModtyTailAspect
modtyTailAspect = Raw.ModtyTailAspect <$> unqWord <*> exprC @Reldtt

instance SysParser Reldtt where
  sysExprC = brackets $ do
    snout <- modtySnout
    tail <- Raw.ModtyTail <$> (many $ pipe *> modtyTailAspect)
    return $ Raw.KnownModty snout tail
