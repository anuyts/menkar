module Menkar.Systems.Reldtt.Fine where

import Menkar.Fine
import Menkar.System

import GHC.Generics

data Reldtt :: KSys where

type instance Mode Reldtt = ReldttMode
type instance Modality Reldtt = ReldttModality
type instance Degree Reldtt = ReldttDegree
type instance SysTerm Reldtt = ReldttTerm

{-| @ReldttModeOne@ and @ReldttModeNull@ are really just modes 1 and 0 (depth 0 and -1) but with a special treatment.
-}
data ReldttMode v = ReldttMode {unMode :: Term Reldtt v}
  deriving (Functor, Foldable, Traversable, Generic1, CanSwallow (Term Reldtt))
newtype ReldttModality v = ReldttModality {unModality :: Term Reldtt v}
  deriving (Functor, Foldable, Traversable, Generic1, CanSwallow (Term Reldtt))
newtype ReldttDegree v = ReldttDegree {unDegree :: Term Reldtt v}
  deriving (Functor, Foldable, Traversable, Generic1, CanSwallow (Term Reldtt))

pattern BareMode d = ReldttMode (Expr2 (TermSys (TermMode d)))
pattern BareFinMode d = BareMode (ModeTermFinite (Expr2 (TermCons d)))
pattern BareModty mu = ReldttModality (Expr2 (TermSys (TermModty mu)))
pattern BareDeg i = ReldttDegree (Expr2 (TermSys (TermDeg i)))

data ModeTerm v = ModeTermFinite (Term Reldtt v) | ModeTermOmega
  deriving (Functor, Foldable, Traversable, Generic1, CanSwallow (Term Reldtt))

data KnownDeg = KnownDegEq | KnownDeg Int | KnownDegTop
data KnownModty = KnownModty Int {-^ Domain -} Int {-^ Codomain -} [KnownDeg]
data ModtyTail v =
  TailEmpty |

  TailDisc   (ReldttMode v) {-^ Tail codomain -} |
  TailCodisc (ReldttMode v) {-^ Tail codomain -} |

  TailForget (ReldttMode v) {-^ Tail domain -} |

  TailDiscForget   (ReldttMode v) {-^ Tail domain -} (ReldttMode v) {-^ Tail codomain -} |
  TailCodiscForget (ReldttMode v) {-^ Tail domain -} (ReldttMode v) {-^ Tail codomain -} |
  TailCont (ReldttMode v)
  deriving (Functor, Foldable, Traversable, Generic1, CanSwallow (Term Reldtt))

data ModtyTerm v =
  ModtyTerm KnownModty (ModtyTail v) |
  
  {-| If @mu : d1 -> d2@ and @nu : d2 -> d3@, then the composite is @'ModtyTermComp' nu d2 mu@ -}
  ModtyTermComp (ReldttModality v) (ReldttMode v) (ReldttModality v) |
  {-| Only for prettyprinting. -} 
  ModtyTermDiv (ReldttModality v) (ReldttModality v) |
  ModtyApproxLeftAdjointProj (ReldttModality v) {-^ The argument modality -} |
  
  {-| Only for prettyprinting. -} 
  ModtyUnavailable (ReldttMode v) {-^ The domain -} (ReldttMode v) {-^ The codomain. -}
  deriving (Functor, Foldable, Traversable, Generic1, CanSwallow (Term Reldtt))

  {-
  {-| @ModtyTermCrisp ddom dcod@ is @< = | =, ..., = > : ddom -> dcod@ -}
  ModtyTermCrisp (Term Reldtt v) (Term Reldtt v) |
  {-| @ModtyTermDiscPar d m n@ is @disc_0^n . fget_0^m = < = | =^n, m, m+1, ..., m+d-1> : m+d -> n+d@ -}
  ModtyTermDiscPar (Term Reldtt v) (Term Reldtt v) (Term Reldtt v) |
  {-| @ModtyTermDiscIrr ddom d n@ is @disc_0^n . irr = < = | =^n, T, T, ..., T > : ddom -> n+d@ -}
  ModtyTermDiscIrr (Term Reldtt v) (Term Reldtt v) (Term Reldtt v) |
  
  {-| @ModtyTermCrispOne dcod@ is @< = | =, ..., = > : one -> dcod@ -}
  ModtyTermCrispOne (Term Reldtt v) |
  {-| @ModtyTermDiscRelOne d n@ is @disc_0^n . rel = < = | =^n, 0, 0, ..., 0 > : one -> n+d@ -}
  ModtyTermDiscRelOne (Term Reldtt v) (Term Reldtt v) |
  {-| @ModtyTermDiscIrrOne d n@ is @disc_0^n . irr = < = | =^n, T, T, ..., T > : one -> n+d@ -}
  ModtyTermDiscIrrOne (Term Reldtt v) (Term Reldtt v) |
  --{-| @ModtyTermCophiRelOne d@ is @cohpi_0 . rel = < 0 | 0, ..., 0 > : one -> d@ -}
  --ModtyTermCophiRelOne (Term Reldtt v) |
  --{-| @ModtyTermDiscIrrCohpiRelOne d@ is @disc_0^n . irr . cohpi_0 . rel = < 0 | 0^n, T, ..., T > : one -> d@ -}
  --ModtyTermDiscIrrCohpiRelOne (Term Reldtt v) |
  --{-| @ModtyTermCophiIrrOne d@ is @cohpi_0 . irr = < T | T, ..., T > : one -> d@ -}
  --ModtyTermCophiIrrOne (Term Reldtt v) |

  {-| @< = | = > : one -> one@ -}
  ModtyTermCrispOneOne |
  {-| @< = | 0 > : one -> one@ -}
  ModtyTermContOneOne |
  {-| @< = | T > : one -> one@ -}
  ModtyTermIrrOneOne |
  --{-| @< 0 | 0 > : one -> one@ -}
  --ModtyTermCohpiRelOneOne |
  --{-| @< 0 | T > : one -> one@ -}
  --ModtyTermIrrCohpiRelOneOne |
  --{-| @< T | T > : one -> one@ -}
  --ModtyTermCophiIrrOneOne |

  {-| @ModtyTermCrispNull dcod@ is @< = | =, ..., = > : null -> dcod@ -}
  ModtyTermCrispNull (Term Reldtt v) |
  {-| @ModtyTermCrispNull d n@ is @< = | =^n, T, ..., T > : null -> n+d@ -}
  ModtyTermDiscIrrNull (Term Reldtt v) (Term Reldtt v) |

  {-| @< = | = > : null -> one@ -}
  ModtyTermCrispNullOne |
  {-| @< = | T > : null -> one@ -}
  ModtyTermIrrNullOne |
  --{-| @< T | T > : null -> one@ -}
  --ModtyTermCohpiIrrNullOne |

  {-| @< = | > : null -> null@ -}
  ModtyTermNullNull |
  
  {-| If @mu : d1 -> d2@ and @nu : d2 -> d3@, then the composite is @'ModtyTermComp' nu d2 mu@ -}
  ModtyTermComp (ReldttModality v) (ReldttMode v) (ReldttModality v) |
  {-| Only for prettyprinting. -} 
  ModtyTermDiv (ReldttModality v) (ReldttModality v) |
  ModtyApproxLeftAdjointProj (ReldttModality v) {-^ The argument modality -} |
  
  {-| Only for prettyprinting. -} 
  ModtyUnavailable (ReldttMode v) {-^ The domain -} (ReldttMode v) {-^ The codomain. -}
  -}
  
  
  {-
  {-| The modality @<> : d -> 0@ mapping presheaves to their set of points. -}
  ModtyTermFinal (ReldttMode v) {-^ The domain -} |
  ModtyTermId (ReldttMode v) {-^ The mode -} |
  {-| If @mu : d1 -> d2@ and @nu : d2 -> d3@, then the composite is @'ModtyTermComp' nu d2 mu@ -}
  ModtyTermComp (ReldttModality v) (ReldttMode v) (ReldttModality v) |
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
  -}

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

data DegTerm v =
  DegEq |
  DegZero |
  {-| Forbidden for terms that might reduce to Top. -}
  DegSuc (ReldttDegree v) |
  DegTop |
  DegGet (ReldttDegree v) (ReldttModality v)
  deriving (Functor, Foldable, Traversable, Generic1, CanSwallow (Term Reldtt))

data ReldttTerm v =
  TermMode (ModeTerm v) |
  TermModty (ModtyTerm v) |
  TermDeg (DegTerm v) |
  {-| Type of modes. -}
  TermTyMode |
  {-| Type of degrees. -}
  TermTyDeg (ReldttMode v) |
  {-| Type of modalities. -}
  TermTyModty (ReldttMode v) (ReldttMode v)
  deriving (Functor, Foldable, Traversable, Generic1, CanSwallow (Term Reldtt))

------------------------------

instance SysTrav Reldtt where
  
instance SysSyntax (Term Reldtt) Reldtt

instance Multimode Reldtt where
  idMod d = BareModty $ ModtyTerm (KnownModty 0 0 []) $ TailCont d
  compMod mu2 dmid mu1 = BareModty $ ModtyTermComp mu2 dmid mu1
  divMod (ModedModality d' mu') (ModedModality d mu) = BareModty $ ModtyTermDiv mu' mu
  crispMod d = BareModty $ ModtyTerm (KnownModty 0 0 []) $ TailDisc d
  dataMode = BareFinMode $ ConsZero
  approxLeftAdjointProj (ModedModality d mu) dcod = BareModty $ ModtyApproxLeftAdjointProj mu

{-
  idMod (ReldttModeNull) = BareModty $ ModtyTermNullNull
  idMod (ReldttModeOne) = BareModty $ ModtyTermContOneOne
  idMod (ReldttMode d) = BareModty $ ModtyTermDiscPar d (Expr2 $ TermCons $ ConsZero) (Expr2 $ TermCons $ ConsZero)
  compMod mu2 dmid mu1 = BareModty $ ModtyTermComp mu2 dmid mu1
  divMod (ModedModality d' mu') (ModedModality d mu) = BareModty $ ModtyTermDiv mu' mu
  crispMod (ReldttModeNull) = BareModty $ ModtyTermNullNull
  crispMod (ReldttModeOne) = BareModty $ ModtyTermCrispNullOne
  crispMod (ReldttMode d) = BareModty $ ModtyTermCrispNull d
  dataMode = ReldttModeNull
  approxLeftAdjointProj (ModedModality d mu) dcod = BareModty $ ModtyApproxLeftAdjointProj mu
-}

instance Degrees Reldtt where
  eqDeg = BareDeg $ DegEq
  maybeTopDeg = Just $ BareDeg $ DegTop
  divDeg (ModedModality d mu) i = BareDeg $ DegGet i mu 
