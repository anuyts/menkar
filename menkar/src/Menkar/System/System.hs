module Menkar.System.System where

import Menkar.System.TC
import Menkar.System.PrettyPrint
import Menkar.System.MagicContext
import Menkar.System.Parser
import Menkar.System.Scoper

class (
  SysTC sys,
  SysFinePretty sys,
  SysMagicContext sys,
  SysParser sys,
  SysScoper sys
  ) => Sys sys where
