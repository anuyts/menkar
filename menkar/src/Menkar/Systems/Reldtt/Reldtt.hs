module Menkar.Systems.Reldtt.Reldtt where

import Menkar.Fine
import Menkar.System

import GHC.Generics

data Reldtt :: KSys where

type instance Mode Reldtt = ReldttMode
type instance Modality Reldtt = ReldttModality
type instance Degree Reldtt = ReldttDegree
type instance SysTerm Reldtt = ReldttTerm

newtype ReldttMode v = ReldttMode (Term Reldtt v)
  deriving (Functor, Foldable, Traversable, Generic)
newtype ReldttModality v = ReldttModality (Term Reldtt v)
  deriving (Functor, Foldable, Traversable, Generic)
newtype ReldttDegree v = ReldttDegree (Term Reldtt v)
  deriving (Functor, Foldable, Traversable, Generic)

data ModtyTerm v =
  ModtyTermId (ReldttMode v) {-^ The mode -} |
  ModtyTermComp (ReldttModality v) (ReldttModality v) {-^ Mathematical order -} |
  ModtyTermPar (ReldttMode v) {-^ The codomain -} |
  ModtyTermDisc (ReldttMode v) {-^ The domain -} |
  ModtyTermPrep0 (ReldttModality v) {-^ The argument modality -} |
  {-| Only for prettyprinting. -} 
  ModtyUnavailable (ReldttMode v) {-^ The domain -} (ReldttMode v) {-^ The codomain. -} |
  ModtyApproxLeftAdjointProj (ReldttModality v) {-^ The argument modality -} |
  ModtyAbs (NamedBinding Term Reldtt v)
  deriving (Functor, Foldable, Traversable, Generic)

data ReldttTerm v =
  TermModty (ModtyTerm v)
  deriving (Functor, Foldable, Traversable, Generic)

instance SysTrav Reldtt where
  
