module Menkar.Fine.Multimode where

import Menkar.Fine.Syntax

class (
    Functor mode,
    Functor modty,
    CanSwallow (Term mode modty) mode,
    CanSwallow (Term mode modty) modty
  ) => Multimode mode modty | mode -> modty, modty -> mode where
  idMod :: mode v -> modty v
  compMod :: modty v -> mode v -> modty v -> modty v
  wildMode :: mode v -- to be abolished!
  flatMod :: modty v
  irrMod :: modty v

class (
    Multimode mode modty,
    Functor rel,
    CanSwallow (Term mode modty) rel
  ) => Degrees mode modty rel | rel -> mode, rel -> modty where
  eqDeg :: rel v

idModedModality :: (Multimode mode modty) => mode v -> ModedModality mode modty v
idModedModality d = ModedModality d (idMod d)

compModedModality :: (Multimode mode modty) =>
  ModedModality mode modty v -> ModedModality mode modty v -> ModedModality mode modty v
compModedModality (ModedModality d' mu') (ModedModality d mu) = ModedModality d (compMod mu' d' mu)
