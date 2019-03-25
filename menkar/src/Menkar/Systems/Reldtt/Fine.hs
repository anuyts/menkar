module Menkar.Systems.Reldtt.Fine where

import Menkar.Fine
import Menkar.System

import GHC.Generics

data Reldtt :: KSys where

type instance Mode Reldtt = ReldttMode
type instance Modality Reldtt = ReldttModality
type instance Degree Reldtt = ReldttDegree
type instance SysTerm Reldtt = ReldttTerm

newtype ReldttMode v = ReldttMode {unMode :: Term Reldtt v}
  deriving (Functor, Foldable, Traversable, Generic1, CanSwallow (Term Reldtt))
newtype ReldttModality v = ReldttModality {unModality :: Term Reldtt v}
  deriving (Functor, Foldable, Traversable, Generic1, CanSwallow (Term Reldtt))
newtype ReldttDegree v = ReldttDegree {unDegree :: Term Reldtt v}
  deriving (Functor, Foldable, Traversable, Generic1, CanSwallow (Term Reldtt))

data ModtyTerm v =
  ModtyTermIdSet {-^ The modality @<> : 0 -> 0@, i.e. the identity functor on the category of sets. -} |
  ModtyTermId (ReldttMode v) {-^ The mode -} |
  ModtyTermComp (ReldttModality v) (ReldttModality v) {-^ Mathematical order -} |
  {-| Only for prettyprinting. -} 
  ModtyTermDiv (ReldttModality v) (ReldttModality v) |
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

--pattern BareMode d = ReldttMode (Expr2 (TermSys (TermMode d)))
pattern BareDeg i = ReldttDegree (Expr2 (TermSys (TermDeg i)))
pattern BareModty mu = ReldttModality (Expr2 (TermSys (TermModty mu)))

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

instance Multimode Reldtt where
  idMod d = BareModty $ ModtyTermId d
  compMod mu2 dmid mu1 = BareModty $ ModtyTermComp mu2 mu1
  divMod (ModedModality d' mu') (ModedModality d mu) = BareModty $ ModtyTermDiv mu' mu
  crispMod d = BareModty $ ModtyAbs dataMode d $ NamedBinding Nothing $ unDegree $ BareDeg $ DegEq
  dataMode = ReldttMode $ Expr2 $ TermCons $ ConsZero
  approxLeftAdjointProj (ModedModality d mu) dcod = BareModty $ ModtyApproxLeftAdjointProj mu
  
instance Degrees Reldtt where
  eqDeg = BareDeg $ DegEq
  maybeTopDeg = Just $ BareDeg $ DegTop
  divDeg (ModedModality d mu) i = BareDeg $ DegGet i mu 
