module Menkar.Systems.Reldtt.Fine where

import Menkar.Fine
import Menkar.System

import GHC.Generics

data Reldtt :: KSys where

type instance Mode Reldtt = Term Reldtt
type instance Modality Reldtt = Term Reldtt
type instance Degree Reldtt = Term Reldtt
type instance SysTerm Reldtt = ReldttSysTerm

{-
{-| @ReldttModeOne@ and @ReldttModeNull@ are really just modes 1 and 0 (depth 0 and -1) but with a special treatment.
-}
newtype ReldttMode v = ReldttMode {unMode :: Term Reldtt v}
  deriving (Functor, Foldable, Traversable, Generic1, CanSwallow (Term Reldtt))
newtype ReldttModality v = ReldttModality {unModality :: Term Reldtt v}
  deriving (Functor, Foldable, Traversable, Generic1, CanSwallow (Term Reldtt))
newtype ReldttDegree v = ReldttDegree {unDegree :: Term Reldtt v}
  deriving (Functor, Foldable, Traversable, Generic1, CanSwallow (Term Reldtt))
-}

pattern BareMode d = Expr2 (TermSys (SysTermMode d))
pattern BareFinMode d = BareMode (ModeTermFinite (Expr2 (TermCons d)))
pattern BareModty mu = Expr2 (TermSys (SysTermModty mu))
pattern BareDeg i = Expr2 (TermSys (SysTermDeg i))

data ModeTerm v = ModeTermFinite (Term Reldtt v) | ModeTermOmega
  deriving (Functor, Foldable, Traversable, Generic1, CanSwallow (Term Reldtt))

data KnownDeg = KnownDegEq | KnownDeg Int | KnownDegTop
data KnownModty = KnownModty Int {-^ Domain -} Int {-^ Codomain -} [KnownDeg] {-^ Degrees in REVERSE ORDER. -}
data ModtyTail v =
  TailEmpty |

  TailDisc   (Term Reldtt v) {-^ Tail codomain, can be omega -} |
  TailCodisc (Term Reldtt v) {-^ Tail codomain, can be omega -} |

  TailForget (Term Reldtt v) {-^ Tail domain, can be omega -} |

  TailDiscForget   (Term Reldtt v) {-^ Tail domain, can be omega -} (Term Reldtt v) {-^ Tail codomain, can be omega -} |
  TailCodiscForget (Term Reldtt v) {-^ Tail domain, can be omega -} (Term Reldtt v) {-^ Tail codomain, can be omega -} |
  TailCont (Term Reldtt v) {-^ Tail domain and codomain, can be omega -}
  deriving (Functor, Foldable, Traversable, Generic1, CanSwallow (Term Reldtt))

extDisc :: KnownModty -> KnownModty
extDisc (KnownModty kdom kcod []) = (KnownModty kdom (kcod + 1) [KnownDegEq])
extDisc (KnownModty kdom kcod (kdeg : kdegs)) = (KnownModty kdom (kcod + 1) (kdeg : kdeg : kdegs))
extCodisc :: KnownModty -> KnownModty
extCodisc (KnownModty kdom kcod kdegs) = (KnownModty kdom (kcod + 1) (KnownDegTop : kdegs))
extForget :: KnownModty -> KnownModty
extForget (KnownModty kdom kcod kdegs) = (KnownModty (kdom + 1) kcod kdegs)

_modtyTail'dom :: ModtyTail v -> Term Reldtt v
_modtyTail'dom TailEmpty = BareFinMode $ ConsZero
_modtyTail'dom (TailDisc dcod) = BareFinMode $ ConsZero
_modtyTail'dom (TailCodisc dcod) = BareFinMode $ ConsZero
_modtyTail'dom (TailForget ddom) = ddom
_modtyTail'dom (TailDiscForget ddom dcod) = ddom
_modtyTail'dom (TailCodiscForget ddom dcod) = ddom
_modtyTail'dom (TailCont d) = d

_modtyTail'cod :: ModtyTail v -> Term Reldtt v
_modtyTail'cod TailEmpty = BareFinMode $ ConsZero
_modtyTail'cod (TailDisc dcod) = dcod
_modtyTail'cod (TailCodisc dcod) = dcod
_modtyTail'cod (TailForget ddom) = BareFinMode $ ConsZero
_modtyTail'cod (TailDiscForget ddom dcod) = dcod
_modtyTail'cod (TailCodiscForget ddom dcod) = dcod
_modtyTail'cod (TailCont d) = d

data ModtyTerm v =
  ModtyTerm KnownModty (ModtyTail v) |
  
  {-| If @mu : d1 -> d2@ and @nu : d2 -> d3@, then the composite is @'ModtyTermComp' nu d2 mu@ -}
  ModtyTermComp (Term Reldtt v) (Term Reldtt v) (Term Reldtt v) |
  {-| Only for prettypring.
      If @mu : d1 -> dcod@ and @rho : d2 -> dcod@, then @'ModtyTermDiv' rho mu@ denotes @rho \ mu : d1 -> d2@ -} 
  ModtyTermDiv (Term Reldtt v) (Term Reldtt v) |
  ModtyTermApproxLeftAdjointProj (Term Reldtt v) {-^ The argument modality -} |
  
  {-| Only for prettyprinting. -} 
  ModtyTermUnavailable (Term Reldtt v) {-^ The domain, can be omega -} (Term Reldtt v) {-^ The codomain, can be omega -}
  deriving (Functor, Foldable, Traversable, Generic1, CanSwallow (Term Reldtt))

data DegTerm v =
  DegEq |
  DegZero |
  {-| Forbidden for terms that might reduce to Top. -}
  DegSuc (Term Reldtt v) |
  DegTop |
  DegGet (Term Reldtt v) {-^ Degree -} (Term Reldtt v) {-^ Modality -}
  deriving (Functor, Foldable, Traversable, Generic1, CanSwallow (Term Reldtt))

data ReldttSysTerm v =
  SysTermMode (ModeTerm v) |
  SysTermModty (ModtyTerm v) |
  SysTermDeg (DegTerm v) |
  {-| Type of modes. -}
  SysTypeMode |
  {-| Type of degrees. -}
  SysTypeDeg (Term Reldtt v) {-^ Mode, can be omega. -} |
  {-| Type of modalities. -}
  SysTypeModty (Term Reldtt v) {-^ Domain, can be omega -} (Term Reldtt v) {-^ Codomain, can be omega -}
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
  approxLeftAdjointProj (ModedModality d mu) dcod = BareModty $ ModtyTermApproxLeftAdjointProj mu

instance Degrees Reldtt where
  eqDeg = BareDeg $ DegEq
  maybeTopDeg = Just $ BareDeg $ DegTop
  divDeg (ModedModality d mu) i = BareDeg $ DegGet i mu 
