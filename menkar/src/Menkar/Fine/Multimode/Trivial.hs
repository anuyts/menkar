module Menkar.Fine.Multimode.Trivial where

import Menkar.Fine.Syntax
import Menkar.Fine.Multimode
import Menkar.PrettyPrint.Fine

import Text.PrettyPrint.Tree

import GHC.Generics (U1 (..))

instance Fine2Pretty U1 U1 Mode where
  fine2pretty gamma (Mode U1) = ribbon "data"
instance Fine2Pretty U1 U1 Modty where
  fine2pretty gamma (Modty U1) = ribbon "hoc"

instance Multimode U1 U1 where
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

instance Degrees U1 U1 U1 where
  eqDeg = U1
  topDeg = U1
  divDeg (ModedModality U1 U1) U1 = U1
  isTopDeg U1 = False
