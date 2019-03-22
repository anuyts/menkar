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
  deriving (Functor, Foldable, Traversable, Generic1, CanSwallow (Term Reldtt))
newtype ReldttModality v = ReldttModality (Term Reldtt v)
  deriving (Functor, Foldable, Traversable, Generic1, CanSwallow (Term Reldtt))
newtype ReldttDegree v = ReldttDegree (Term Reldtt v)
  deriving (Functor, Foldable, Traversable, Generic1, CanSwallow (Term Reldtt))

data ModtyTerm v =
  ModtyTermIdSet {-^ The modality @<> : 0 -> 0@, i.e. the identity functor on the category of sets. -} |
  ModtyTermId (ReldttMode v) {-^ The mode -} |
  ModtyTermComp (ReldttModality v) (ReldttModality v) {-^ Mathematical order -} |
  --ModtyTermPar (ReldttMode v) {-^ The codomain -} |
  --ModtyTermDisc (ReldttMode v) {-^ The domain -} |
  --ModtyTermPrep0 (ReldttModality v) {-^ The argument modality -} |
  {-| Only for prettyprinting. -} 
  ModtyUnavailable (ReldttMode v) {-^ The domain -} (ReldttMode v) {-^ The codomain. -} |
  ModtyApproxLeftAdjointProj (ReldttModality v) {-^ The argument modality -} |
  {-| @'ModtyPrep' d mu@ represents @<d, 0*mu, ..., n*mu>@.
      Forbidden for combinations that after reduction might create non-monotonous modalities. -}
  ModtyPrep (ReldttDegree v) (ReldttModality v) |
  {-| Forbidden for expressions that might reduce to something non-monotonous. -}
  ModtyAbs (ReldttMode v) {-^ The domain -} (ReldttMode v) {-^ The codomain. -} (NamedBinding Term Reldtt v)
  deriving (Functor, Foldable, Traversable, Generic1, CanSwallow (Term Reldtt))

data DegTerm v =
  DegEq |
  DegZero |
  {-| Forbidden for terms that might reduce to Top. -}
  DegSuc (ReldttDegree v) |
  DegTop |
  DegGet (ReldttDegree v) (ReldttModality v)
  deriving (Functor, Foldable, Traversable, Generic1, CanSwallow (Term Reldtt))

data ReldttTerm v =
  TermModty (ModtyTerm v) |
  TermDeg (DegTerm v)
  deriving (Functor, Foldable, Traversable, Generic1, CanSwallow (Term Reldtt))

instance SysTrav Reldtt where
  
instance SysSyntax (Term Reldtt) Reldtt
