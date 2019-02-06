module Menkar.Fine.Multimode where

import Prelude hiding (divMod)

import Menkar.Fine.Syntax

class (SysSyntax (Term sys) sys) => Multimode sys where
  idMod :: Mode sys v -> Modality sys v
  compMod :: (Modality sys) v -> (Mode sys) v -> (Modality sys) v -> (Modality sys) v
  divMod :: ModedModality sys v -> ModedModality sys v -> Modality sys v
  wildMode :: (Mode sys) v -- to be abolished!
  wildModty :: (Modality sys) v -- to be abolished!
  flatMod :: (Modality sys) v
  dataMode :: (Mode sys) v
  -- | When applied to mu, this yields the greatest modality less than the left adjoint functor to mu.
  approxLeftAdjointProj :: ModedModality sys v -> (Mode sys) v {-^ the codomain -} -> (Modality sys) v
  -- | True if @mu . nu <= id@, where nu is the @approxLeftAdjointProj@.
  sigmaHasEta :: ModedModality sys v -> (Mode sys) v {-^ the codomain -} -> Bool

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

divModedModality :: (Multimode sys) =>
  ModedModality sys v -> ModedModality sys v -> ModedModality sys v
divModedModality d'mu' dmu@(ModedModality d mu) = ModedModality d (divMod d'mu' dmu)

flatModedModality :: (Multimode sys) => ModedModality sys v
flatModedModality = ModedModality dataMode flatMod

wildModedModality :: (Multimode sys) => ModedModality sys v
wildModedModality = ModedModality wildMode wildModty

modedApproxLeftAdjointProj :: (Multimode sys) =>
  ModedModality sys v -> (Mode sys) v {-^ the codomain -} -> ModedModality sys v
modedApproxLeftAdjointProj dmu d' = ModedModality d' $ approxLeftAdjointProj dmu d'
