module Menkar.Fine.Syntax.System where

import Menkar.Fine.Syntax.Substitution
import Data.Kind

type KSys = *

type family Mode (sys :: KSys) = (mode :: * -> *) | mode -> sys
type family Modality (sys :: KSys) = (modality :: * -> *) | modality -> sys
type family Degree (sys :: KSys) = (degree :: * -> *) | degree -> sys

class (Traversable (Mode sys),
       Traversable (Modality sys),
       Traversable (Degree sys))
      => SysTrav sys

class (SysTrav sys,
       CanSwallow t (Mode sys),
       CanSwallow t (Modality sys),
       CanSwallow t (Degree sys))
      => SysSyntax t sys
