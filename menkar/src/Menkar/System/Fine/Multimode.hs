module Menkar.System.Fine.Multimode where

import Prelude hiding (divMod)

import Menkar.Fine.Syntax
import Menkar.System.Fine.Syntax

class (SysSyntax (Term sys) sys) => Multimode sys where
  idMod :: Mode sys v -> Modality sys v
  compMod :: (Modality sys) v -> (Modality sys) v -> (Modality sys) v
  -- | Only for use by the prettyprinter. Good behaviour w.r.t. inequality checking is not required.
  divMod :: ModedModality sys v -> ModedModality sys v -> Modality sys v
  crispMod :: Mode sys v {-^ Codomain. -} -> (Modality sys) v
  dataMode :: (Mode sys) v
  -- | When applied to mu, this yields the greatest modality less than the left adjoint functor to mu.
  approxLeftAdjointProj :: ModedModality sys v -> (Modality sys) v
  _modality'dom :: Modality sys v -> Mode sys v
  _modality'cod :: Modality sys v -> Mode sys v
  --term2mode :: Term sys v -> Mode sys v
  --term2modty :: Term sys v -> Modality sys v

class (SysSyntax (Term sys) sys, Multimode sys) => Degrees sys where
  eqDeg :: Mode sys v -> (Degree sys) v
  maybeTopDeg :: Mode sys v -> Maybe (Degree sys v)
  divDeg :: ModedModality sys v -> ModedDegree sys v -> (Degree sys) v
  _degree'mode :: Degree sys v -> Mode sys v
  --These belong to type-checking and may get stuck on metas:
  --isTopDeg :: (Degree sys) v -> Bool
  --isEqDeg :: (Degree sys) v -> Bool

--------------

idModedModality :: (Multimode sys) => (Mode sys) v -> ModedModality sys v
idModedModality = idMod
--idModedModality d = ModedModality d d (idMod d)

compModedModality :: (Multimode sys) =>
  ModedModality sys v -> ModedModality sys v -> ModedModality sys v
compModedModality = compMod
--compModedModality (ModedModality dmid dcod mu2) (ModedModality ddom dmid' mu1) = ModedModality ddom dcod (compMod mu2 dmid mu1)

concatModedModalityDiagrammatically :: (Multimode sys) =>
  [ModedModality sys v] -> Mode sys v {-^ Codomain of the result -} -> ModedModality sys v
concatModedModalityDiagrammatically [] d = idModedModality d
concatModedModalityDiagrammatically (dmu : dmus) d =
  compModedModality (concatModedModalityDiagrammatically dmus d) dmu

divModedModality :: (Multimode sys) =>
  ModedModality sys v -> ModedModality sys v -> ModedModality sys v
divModedModality = divMod
--divModedModality dmu'@(ModedModality ddom' dcod' mu') dmu@(ModedModality ddom dcod mu) =
--  ModedModality ddom ddom' (divMod dmu' dmu)

crispModedModality :: (Multimode sys) => Mode sys v -> ModedModality sys v
crispModedModality = crispMod
--crispModedModality d = ModedModality dataMode d (crispMod d)

modedApproxLeftAdjointProj :: (Multimode sys) =>
  ModedModality sys v -> ModedModality sys v
modedApproxLeftAdjointProj = approxLeftAdjointProj
--modedApproxLeftAdjointProj dmu@(ModedModality ddom dcod mu) = ModedModality dcod ddom $ approxLeftAdjointProj dmu

modedDivDeg :: (Degrees sys) =>
  ModedModality sys v -> ModedDegree sys v -> ModedDegree sys v
modedDivDeg = divDeg
--modedDivDeg dmu ddeg = ModedDegree (modality'dom dmu) $ divDeg dmu ddeg

modedEqDeg :: Degrees sys => Mode sys v -> ModedDegree sys v
modedEqDeg = eqDeg
--modedEqDeg d = ModedDegree d (eqDeg d)

maybeModedTopDeg :: Degrees sys => Mode sys v -> Maybe (ModedDegree sys v)
maybeModedTopDeg = maybeTopDeg
--maybeModedTopDeg d = ModedDegree d <$> maybeTopDeg d

pattern ModedModality dom cod mu <- mu@((\ x -> (_modality'dom x, _modality'cod x)) -> (dom, cod))
--{-# COMPLETE_PATTERNS ModedModality #-}
pattern ModedDegree d deg <- deg@(_degree'mode -> d)
--{-# COMPLETE_PATTERNS ModedDegree #-}
