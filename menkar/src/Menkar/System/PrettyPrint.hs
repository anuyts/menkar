module Menkar.System.PrettyPrint where

import Menkar.System.Fine
import Menkar.Fine.Syntax
import Menkar.PrettyPrint.Fine.Class

import Text.PrettyPrint.Tree

class (SysSyntax (Term sys) sys,
       Fine2Pretty sys (Mode sys),
       Fine2Pretty sys (Modality sys),
       Fine2Pretty sys (Degree sys),
       Fine2Pretty sys (SysTerm sys),
       Fine2Pretty sys (SysUniHSConstructor sys)) => SysPretty sys where
  sysJud2pretty :: Multimode sys =>
    SysJudgement sys -> Fine2PrettyOptions sys -> PrettyTree String
