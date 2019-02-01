module Menkar.Fine.Multimode where

import Menkar.Fine.Syntax

class (SysSyntax (Term sys) sys) => Multimode sys where
  idMod :: Mode sys v -> Modality sys v
  compMod :: (Modality sys) v -> (Mode sys) v -> (Modality sys) v -> (Modality sys) v
  wildMode :: (Mode sys) v -- to be abolished!
  wildModty :: (Modality sys) v -- to be abolished!
  flatMod :: (Modality sys) v
  -- right adjoint to flatMod
  irrMod :: (Modality sys) v
  dataMode :: (Mode sys) v
  approxLeftAdjointProj :: ModedModality sys v -> (Mode sys) v {-^ the codomain -} -> (Modality sys) v
  sigmaHasEta :: ModedModality sys v -> (Mode sys) v {-^ the codomain -} -> Bool
  divModedModality :: ModedModality sys v -> ModedModality sys v -> ModedModality sys v

class (SysSyntax (Term sys) sys, Multimode sys) => Degrees sys where
  eqDeg :: (Degree sys) v
  topDeg :: (Degree sys) v
  divDeg :: ModedModality sys v -> (Degree sys) v -> (Degree sys) v
  isTopDeg :: (Degree sys) v -> Bool
  isEqDeg :: (Degree sys) v -> Bool

--------------

idModedModality :: (Multimode sys) => (Mode sys) v -> ModedModality sys v
idModedModality d = ModedModality d (idMod d)

compModedModality :: (Multimode sys) =>
  ModedModality sys v -> ModedModality sys v -> ModedModality sys v
compModedModality (ModedModality d' mu') (ModedModality d mu) = ModedModality d (compMod mu' d' mu)

irrModedModality :: (Multimode sys) => ModedModality sys v
irrModedModality = ModedModality dataMode irrMod

wildModedModality :: (Multimode sys) => ModedModality sys v
wildModedModality = ModedModality wildMode wildModty

modedApproxLeftAdjointProj :: (Multimode sys) =>
  ModedModality sys v -> (Mode sys) v {-^ the codomain -} -> ModedModality sys v
modedApproxLeftAdjointProj dmu d' = ModedModality d' $ approxLeftAdjointProj dmu d'
