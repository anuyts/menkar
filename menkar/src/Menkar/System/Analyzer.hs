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
       AnalyzerExtraInput (Mode sys) ~ U1,
       AnalyzerExtraInput (Modality sys) ~ U1,
       AnalyzerExtraInput (Degree sys) ~ U1,
       AnalyzerExtraInput (SysTerm sys) ~ U1,
       AnalyzerExtraInput (SysUniHSConstructor sys) ~ U1
      ) => SysAnalyzer sys where
  quickEqSysUnanalyzable :: forall v .
    (DeBruijnLevel v) =>
    SysAnalyzerError sys -> SysTerm sys v -> SysTerm sys v -> Bool

--type instance Classif (Mode sys) = U1
--type instance Classif (Modality sys) = Mode sys :*: Mode sys
