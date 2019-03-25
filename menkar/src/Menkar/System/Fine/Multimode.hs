module Menkar.System.Fine.Multimode where

import Prelude hiding (divMod)

import Menkar.Fine.Syntax
import Menkar.System.Fine.Syntax

class (SysSyntax (Term sys) sys) => Multimode sys where
  idMod :: Mode sys v -> Modality sys v
  compMod :: (Modality sys) v -> (Mode sys) v -> (Modality sys) v -> (Modality sys) v
  -- | Only for use by the prettyprinter. Good behaviour w.r.t. inequality checking is not required.
  divMod :: ModedModality sys v -> ModedModality sys v -> Modality sys v
  crispMod :: Mode sys v {-^ Codomain. -} -> (Modality sys) v
  dataMode :: (Mode sys) v
  -- | When applied to mu, this yields the greatest modality less than the left adjoint functor to mu.
  approxLeftAdjointProj :: ModedModality sys v -> (Mode sys) v {-^ the codomain -} -> (Modality sys) v
  --term2mode :: Term sys v -> Mode sys v
  --term2modty :: Term sys v -> Modality sys v

class (SysSyntax (Term sys) sys, Multimode sys) => Degrees sys where
  eqDeg :: (Degree sys) v
  maybeTopDeg :: Maybe (Degree sys v)
  divDeg :: ModedModality sys v -> (Degree sys) v -> (Degree sys) v
  --These belong to type-checking and may get stuck on metas:
  --isTopDeg :: (Degree sys) v -> Bool
  --isEqDeg :: (Degree sys) v -> Bool

--------------

idModedModality :: (Multimode sys) => (Mode sys) v -> ModedModality sys v
idModedModality d = ModedModality d (idMod d)

compModedModality :: (Multimode sys) =>
  ModedModality sys v -> ModedModality sys v -> ModedModality sys v
compModedModality (ModedModality d' mu') (ModedModality d mu) = ModedModality d (compMod mu' d' mu)

concatModedModalityDiagrammatically :: (Multimode sys) =>
  [ModedModality sys v] -> Mode sys v {-^ Codomain of the result -} -> ModedModality sys v
concatModedModalityDiagrammatically [] d = idModedModality d
concatModedModalityDiagrammatically (dmu : dmus) d =
  compModedModality (concatModedModalityDiagrammatically dmus d) dmu

divModedModality :: (Multimode sys) =>
  ModedModality sys v -> ModedModality sys v -> ModedModality sys v
divModedModality d'mu' dmu@(ModedModality d mu) = ModedModality d (divMod d'mu' dmu)

crispModedModality :: (Multimode sys) => Mode sys v -> ModedModality sys v
crispModedModality d = ModedModality dataMode (crispMod d)

modedApproxLeftAdjointProj :: (Multimode sys) =>
  ModedModality sys v -> (Mode sys) v {-^ the codomain -} -> ModedModality sys v
modedApproxLeftAdjointProj dmu d' = ModedModality d' $ approxLeftAdjointProj dmu d'
