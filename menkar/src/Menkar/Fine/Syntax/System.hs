module Menkar.Fine.Syntax.System where

import Menkar.Fine.Syntax.Substitution
import Data.Kind

type KSys = *

--type family Mode :: KSys -> * -> *
--type family Modality :: KSys -> * -> *
--type family Degree :: KSys -> * -> *

{-| Modes (potentially nonsensical).
-}
type family Mode (sys :: KSys) = (mode :: * -> *) | mode -> sys

{-| Modalities (potentially nonsensical for some or all source & target modes).
-}
type family Modality (sys :: KSys) = (modality :: * -> *) | modality -> sys

{-| Degree (potentially nonsensical for some or all modes).
-}
type family Degree (sys :: KSys) = (degree :: * -> *) | degree -> sys

type family SysTerm (sys :: KSys) = (sysTermNV :: * -> *) | sysTermNV -> sys

type family SysJudgement (sys :: KSys) = (sysJudgement :: *) | sysJudgement -> sys

class (Traversable (Mode sys),
       Traversable (Modality sys),
       Traversable (Degree sys),
       Traversable (SysTerm sys))
      => SysTrav sys

class (SysTrav sys,
       CanSwallow t (Mode sys),
       CanSwallow t (Modality sys),
       CanSwallow t (Degree sys),
       CanSwallow t (SysTerm sys))
      => SysSyntax t sys
