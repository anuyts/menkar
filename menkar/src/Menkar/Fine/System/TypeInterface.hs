module Menkar.Fine.System.TypeInterface where

import Menkar.Fine.Syntax.Substitution
import Data.Kind

type KSys = *

type family Mode :: KSys -> * -> *
type family Modality :: KSys -> * -> *
type family Degree :: KSys -> * -> *

class (Traversable (Mode sys),
       Traversable (Modality sys),
       Traversable (Degree sys))
      => TravSys sys

class (TravSys sys,
       CanSwallow t (Mode sys),
       CanSwallow t (Modality sys),
       CanSwallow t (Degree sys))
      => PreSys t sys
