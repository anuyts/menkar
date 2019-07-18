module Menkar.System.PrettyPrint.Raw where

import Menkar.Basic
import Menkar.Raw
import Menkar.PrettyPrint.Raw.Class

class (Unparsable (SysExprC sys)
  ) => SysRawPretty (sys :: KSys) where
