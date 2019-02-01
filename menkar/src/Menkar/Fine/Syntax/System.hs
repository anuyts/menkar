module Menkar.Fine.Syntax.System where

import Menkar.Fine.Syntax.Substitution
import Data.Kind

type KSys = *

type family Mode :: KSys -> * -> *
type family Modality :: KSys -> * -> *
type family Degree :: KSys -> * -> *

class (Traversable (Mode sys),
       Traversable (Modality sys),
       Traversable (Degree sys))
      => SysTrav sys

class (SysTrav sys,
       CanSwallow t (Mode sys),
       CanSwallow t (Modality sys),
       CanSwallow t (Degree sys))
      => SysSyntax t sys
