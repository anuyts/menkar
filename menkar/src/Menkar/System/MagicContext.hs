module Menkar.System.MagicContext where

import Menkar.System.Basic
import Menkar.Fine.Syntax
import Menkar.Fine.Context

import Data.Void
import GHC.Generics

class SysMagicContext sys where
  magicModule :: ModuleRHS sys Void
