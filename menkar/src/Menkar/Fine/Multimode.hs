module Menkar.Fine.Multimode where

import Menkar.Fine.Syntax
import Menkar.Fine.Substitution

class (
    Functor mode,
    Functor modty,
    CanSwallow (Term mode modty) mode,
    CanSwallow (Term mode modty) modty
  ) => Multimode mode modty where
  idMod :: mode v -> modty v
  compMod :: modty v -> mode v -> modty v -> modty v
