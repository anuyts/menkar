module Menkar.System.Analyzer where

import Menkar.Fine.Syntax
import Menkar.System.Fine
import Menkar.Analyzer.Class
import Menkar.Fine.Context

import GHC.Generics
import Data.Functor.Const

class (SysSyntax (Term sys) sys,
       Analyzable sys (Mode sys),
       Analyzable sys (Modality sys),
       Analyzable sys (Degree sys),
       Analyzable sys (SysTerm sys),
       Analyzable sys (SysUniHSConstructor sys),
       Classif (Mode sys) ~ U1,
       Classif (Modality sys) ~ (Mode sys :*: Mode sys), -- domain and codomain
       Relation (Mode sys) ~ U1,
       Relation (Modality sys) ~ Const ModRel
      ) => SysAnalyzer sys where

--type instance Classif (Mode sys) = U1
--type instance Classif (Modality sys) = Mode sys :*: Mode sys
