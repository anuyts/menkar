module Menkar.Systems.Reldtt.Reldtt where

import Menkar.Fine
import Menkar.System

data Reldtt :: KSys where

type instance Mode Reldtt = ReldttMode
type instance Modality Reldtt = ReldttModality
type instance Degree Reldtt = ReldttTerm

newtype ReldttMode v = ReldttMode (Term Reldtt v)
newtype ReldttModality v = ReldttModality (Term Reldtt v)
newtype ReldttDegree v = ReldttDegree (Term Reldtt v)

data ModtyTerm v =
  ModtyTermId (ReldttMode v) {-^ The mode -} |
  ModtyTermComp (ReldttModality v) (ReldttModality v) {-^ Mathematical order -} |
  ModtyTermPar (ReldttMode v) {-^ The codomain -} |
  ModtyTermDisc (ReldttMode v) {-^ The domain -} |
  ModtyTermPrep0 (ReldttModality v) {-^ The argument modality -} |
  ModtyUnavailable (ReldttMode v) {-^ The domain -} (ReldttMode v) {-^ The codomain; only for prettyprinting. -} |
  ModtyApproxLeftAdjointProj (ReldttModality v) {-^ The argument modality -}

data ReldttTerm v =
  TermModty (ModtyTerm v)
  
