{-# LANGUAGE AllowAmbiguousTypes #-}

module Menkar.System.Parser where

import Menkar.Parser.Class
import Menkar.System.Basic
import qualified Menkar.Raw as Raw

class SysParser (sys :: KSys) where
  sysExprC :: CanParse m => m (Raw.SysExprC sys)
