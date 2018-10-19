module Menkar.Fine.Multimode where

import Menkar.Fine.Syntax

class (
    Functor mode,
    Functor modty,
    CanSwallow (Term mode modty) mode,
    CanSwallow (Term mode modty) modty
  ) => Multimode mode modty where
  idMod :: mode v -> modty v
  compMod :: modty v -> mode v -> modty v -> modty v

class (
    Multimode mode modty,
    Functor rel,
    CanSwallow (Term mode modty) rel
  ) => Degrees mode modty rel | rel -> mode, rel -> modty where
  eqDeg :: rel v
