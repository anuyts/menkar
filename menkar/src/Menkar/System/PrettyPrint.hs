module Menkar.System.PrettyPrint where

import Menkar.System.Fine
import Menkar.System.Analyzer
import Menkar.Fine.Syntax
import Menkar.PrettyPrint.Aux.Context
import Menkar.PrettyPrint.Fine.Class
import Menkar.Basic.Context
import Menkar.Analyzer

import Text.PrettyPrint.Tree
import Data.Void

class (SysAnalyzer sys,
       Fine2Pretty sys (Mode sys),
       Fine2Pretty sys (Modality sys),
       Fine2Pretty sys (Degree sys),
       Fine2Pretty sys (SysTerm sys),
       Fine2Pretty sys (SysUniHSConstructor sys)) => SysPretty sys where
  sysJud2pretty :: Multimode sys =>
    SysJudgement sys -> Fine2PrettyOptions sys -> PrettyTree String
  sysToken2string :: forall t . SysAnalyzableToken sys t -> String
  sysClassif2pretty :: forall t v .
    (DeBruijnLevel v, Multimode sys, Analyzable sys t) =>
    SysAnalyzableToken sys t ->
    ScCtx sys v Void ->
    ClassifExtraInput t v ->
    Classif t v ->
    ClassifExtraInput (Classif t) v ->
    Fine2PrettyOptions sys ->
    PrettyTree String
  sysHaveFine2Pretty :: forall t a . SysAnalyzableToken sys t -> (Fine2Pretty sys t => a) -> a
