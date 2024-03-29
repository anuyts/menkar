module Menkar.System.Analyzer where

import Menkar.Fine.Syntax
import Menkar.System.Fine
import Menkar.Analyzer.Class
import Menkar.Fine.Context

import GHC.Generics
import Data.Functor.Const

class (SysSyntax (Term sys) sys,
       Multimode sys,
       Degrees sys,
       Analyzable sys (Mode sys),
       Analyzable sys (Modality sys),
       Analyzable sys (Degree sys),
       Analyzable sys (SysTerm sys),
       Analyzable sys (SysUniHSConstructor sys),
       Classif (Mode sys) ~ U1,
       Classif (Modality sys) ~ (Mode sys :*: Mode sys), -- domain and codomain
       Classif (Degree sys) ~ Mode sys,
       Classif (SysTerm sys) ~ Type sys,
       Classif (SysUniHSConstructor sys) ~ Classif (UniHSConstructor sys),
       Relation (Mode sys) ~ U1,
       Relation (Modality sys) ~ Const ModRel,
       Relation (Degree sys) ~ Const ModRel,
       Relation (SysTerm sys) ~ ModedDegree sys,
       Relation (SysUniHSConstructor sys) ~ Relation (UniHSConstructor sys),
       ClassifExtraInput (Mode sys) ~ U1,
       ClassifExtraInput (Modality sys) ~ U1,
       ClassifExtraInput (Degree sys) ~ U1,
       ClassifExtraInput (SysTerm sys) ~ U1,
       ClassifExtraInput (SysUniHSConstructor sys) ~ U1
      ) => SysAnalyzer sys where

  -- | See Menkar.TC.QuickEq.quickEq
  quickEqSysUnanalyzable :: forall t v . 
    (Analyzable sys t, DeBruijnLevel v) =>
    SysAnalyzerError sys ->
    AnalyzableToken sys t ->
    t v ->
    t v ->
    ClassifExtraInput t v ->
    ClassifExtraInput t v ->
    Bool

--type instance Classif (Mode sys) = U1
--type instance Classif (Modality sys) = Mode sys :*: Mode sys
