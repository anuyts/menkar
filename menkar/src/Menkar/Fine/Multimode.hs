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
  -- right adjoint to flatMod
  irrMod :: modty v
  dataMode :: mode v
  approxLeftAdjointProj :: ModedModality mode modty v -> mode v {-^ the codomain -} -> modty v
  sigmaHasEta :: ModedModality mode modty v -> mode v {-^ the codomain -} -> Bool
  divModedModality :: ModedModality mode modty v -> ModedModality mode modty v -> ModedModality mode modty v

class (
    Multimode mode modty,
    Functor rel,
    CanSwallow (Term mode modty) rel
  ) => Degrees mode modty rel | rel -> mode, rel -> modty where
  eqDeg :: rel v
  topDeg :: rel v
  divDeg :: ModedModality mode modty v -> rel v -> rel v
  isTopDeg :: rel v -> Bool

--------------

idModedModality :: (Multimode mode modty) => mode v -> ModedModality mode modty v
idModedModality d = ModedModality d (idMod d)

compModedModality :: (Multimode mode modty) =>
  ModedModality mode modty v -> ModedModality mode modty v -> ModedModality mode modty v
compModedModality (ModedModality d' mu') (ModedModality d mu) = ModedModality d (compMod mu' d' mu)

irrModedModality :: (Multimode mode modty) => ModedModality mode modty v
irrModedModality = ModedModality dataMode irrMod

modedApproxLeftAdjointProj :: (Multimode mode modty) =>
  ModedModality mode modty v -> mode v {-^ the codomain -} -> ModedModality mode modty v
modedApproxLeftAdjointProj dmu d' = ModedModality d' $ approxLeftAdjointProj dmu d'
