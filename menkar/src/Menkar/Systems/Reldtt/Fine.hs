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
  {-| The modality @<> : d -> 0@ mapping presheaves to their set of points. -}
  ModtyTermFinal (ReldttMode v) {-^ The domain -} |
  ModtyTermId (ReldttMode v) {-^ The mode -} |
  {-| If @mu : d1 -> d2@ and @nu : d2 -> d3@, then the composite is @'ModtyTermComp' d3 nu d2 mu d1@ -}
  ModtyTermComp (ReldttMode v) (ReldttModality v) (ReldttMode v) (ReldttModality v) (ReldttMode v) |
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

{-
_modtyTerm'dom :: ModtyTerm v -> ReldttMode v
_modtyTerm'dom (ModtyTermFinal ddom) = ddom
_modtyTerm'dom (ModtyTermId d) = d
_modtyTerm'dom (ModtyTermComp nu mu) = _modtyTerm'dom mu
_modtyTerm'dom (ModtyTermDiv rho mu) = _modtyTerm'dom mu
_modtyTerm'dom (ModtyUnavailable ddom dcod) = ddom
_modtyTerm'dom (ModtyApproxLeftAdjointProj mu) = _modtyTerm'cod mu
_modtyTerm'dom (ModtyPrep deg mu) = _modtyTerm'dom mu
_modtyTerm'dom (ModtyAbs ddom dcod namedBinding) = ddom

_modtyTerm'cod :: ModtyTerm v -> ReldttMode v
_modtyTerm'cod (ModtyTermFinal ddom) = BareMode d
_modtyTerm'cod (ModtyTermId d) = d
_modtyTerm'cod (ModtyTermComp nu mu) = _modtyTerm'cod nu
_modtyTerm'cod (ModtyTermDiv rho mu) = _modtyTerm'dom rho
_modtyTerm'cod (ModtyUnavailable ddom dcod) = dcod
_modtyTerm'cod (ModtyApproxLeftAdjointProj mu) = _modtyTerm'dom mu
_modtyTerm'cod (ModtyPrep deg mu) = BareMode $ ConsSuc $ unMode $ _modtyTerm'cod mu
_modtyTerm'cod (ModtyAbs ddom dcod namedBinding) = dcod
-}

pattern BareDeg i = ReldttDegree (Expr2 (TermSys (TermDeg i)))
pattern BareMode d = ReldttMode (Expr2 (TermCons d))
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

------------------------------

instance SysTrav Reldtt where
  
instance SysSyntax (Term Reldtt) Reldtt

instance Multimode Reldtt where
  idMod d = BareModty $ ModtyTermId d
  compMod dcod mu2 dmid mu1 ddom = BareModty $ ModtyTermComp dcod mu2 dmid mu1 ddom
  divMod (ModedModality d' mu') (ModedModality d mu) = BareModty $ ModtyTermDiv mu' mu
  crispMod d = BareModty $ ModtyAbs dataMode d $ NamedBinding Nothing $ unDegree $ BareDeg $ DegEq
  dataMode = ReldttMode $ Expr2 $ TermCons $ ConsZero
  approxLeftAdjointProj (ModedModality d mu) dcod = BareModty $ ModtyApproxLeftAdjointProj mu
  
instance Degrees Reldtt where
  eqDeg = BareDeg $ DegEq
  maybeTopDeg = Just $ BareDeg $ DegTop
  divDeg (ModedModality d mu) i = BareDeg $ DegGet i mu 
