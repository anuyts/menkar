module Menkar.Systems.Trivial.Fine where

import Menkar.Fine.Syntax
import Menkar.Fine.Multimode
import Menkar.PrettyPrint.Fine.Syntax

import Text.PrettyPrint.Tree

import GHC.Generics (U1 (..))

data Trivial :: KSys where

type instance Mode Trivial = U1
type instance Modality Trivial = U1
type instance Degree Trivial = U1

instance SysTrav Trivial where

instance SysSyntax (Term Trivial) Trivial where

  
instance Fine2Pretty Trivial U1 where
  fine2pretty gamma U1 opts = ribbon "*"
--instance Fine2Pretty Trivial U1 where
--  fine2pretty gamma U1 = ribbon "hoc"
  
instance Multimode Trivial where
  idMod U1 = U1
  compMod U1 U1 U1 = U1
  wildMode = U1
  wildModty = U1
  flatMod = U1
  irrMod = U1
  dataMode = U1
  approxLeftAdjointProj (ModedModality U1 U1) U1 = U1
  sigmaHasEta (ModedModality U1 U1) U1 = True
  divModedModality (ModedModality U1 U1) (ModedModality U1 U1) = (ModedModality U1 U1)

trivModedModality = ModedModality U1 U1

instance Degrees Trivial where
  eqDeg = U1
  topDeg = U1
  divDeg (ModedModality U1 U1) U1 = U1
  isTopDeg U1 = False
  isEqDeg U1 = True
