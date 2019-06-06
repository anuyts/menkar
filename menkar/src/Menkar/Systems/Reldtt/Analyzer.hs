module Menkar.Systems.Reldtt.Analyzer where

import Menkar.Fine
import Menkar.System
import Menkar.Systems.Reldtt.Fine

import Control.Exception.AssertFalse

import GHC.Generics
import Util
import Data.Functor.Compose
import Control.Lens

instance SysAnalyzer Reldtt where
  quickEqSysUnanalyzable sysError t1 t2 extraT1 extraT2 = _
