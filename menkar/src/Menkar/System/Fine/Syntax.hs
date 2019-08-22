module Menkar.System.Fine.Syntax where

import Menkar.System.Basic
import Menkar.Fine.Syntax.Substitution

import Control.DeepSeq.Picky

import Data.Kind

--type family Mode :: KSys -> * -> *
--type family Modality :: KSys -> * -> *
--type family Degree :: KSys -> * -> *

{-| Modes (potentially nonsensical).
-}
type family Mode (sys :: KSys) = (mode :: * -> *) | mode -> sys

{-| Modalities (potentially nonsensical for some or all source & target modes).
    The general idea is that if you know a modality, then its domain and codomain can be inferred.
    Moreover, the type system may equate modalities WITHOUT asserting that their domain and codomain are equal.
-}
type family Modality (sys :: KSys) = (modality :: * -> *) | modality -> sys

{-| Degree (potentially nonsensical for some or all modes).
-}
type family Degree (sys :: KSys) = (degree :: * -> *) | degree -> sys

type family SysTerm (sys :: KSys) = (sysTerm :: * -> *) | sysTerm -> sys

type family SysUniHSConstructor (sys :: KSys) = (sysUniHSConstructor :: * -> *) | sysUniHSConstructor -> sys

type family SysJudgement (sys :: KSys) = (sysJudgement :: *) | sysJudgement -> sys

type family SysAnalyzerError (sys :: KSys) = (sysAnalyzer :: *) | sysAnalyzer -> sys

type family SysAnalyzableToken (sys :: KSys) = (sysToken :: (* -> *) -> *) | sysToken -> sys

class (NFData1 (Mode sys),
       NFData1 (Modality sys),
       NFData1 (Degree sys),
       NFData1 (SysTerm sys),
       NFData1 (SysUniHSConstructor sys))
      => SysNF sys where

class (SysNF sys,
       Traversable (Mode sys),
       Traversable (Modality sys),
       Traversable (Degree sys),
       Traversable (SysTerm sys),
       Traversable (SysUniHSConstructor sys))
      => SysTrav sys where

-- Terms have not been defined at this point.
class (SysTrav sys,
       CanSwallow t (Mode sys),
       CanSwallow t (Modality sys),
       CanSwallow t (Degree sys),
       CanSwallow t (SysTerm sys),
       CanSwallow t (SysUniHSConstructor sys))
      => SysSyntax t sys where
