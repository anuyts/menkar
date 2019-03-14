module Menkar.System.PrettyPrint where

import Menkar.System.Fine
import Menkar.Fine.Syntax
import Menkar.PrettyPrint.Fine.Class

class (SysSyntax (Term sys) sys,
       Fine2Pretty sys (Mode sys),
       Fine2Pretty sys (Modality sys),
       Fine2Pretty sys (Degree sys),
       Fine2Pretty sys (SysTerm sys)) => SysPretty sys where
