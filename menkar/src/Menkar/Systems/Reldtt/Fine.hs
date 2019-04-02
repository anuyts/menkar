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

instance Degrees Reldtt where
  eqDeg = BareDeg $ DegEq
  maybeTopDeg = Just $ BareDeg $ DegTop
  divDeg (ModedModality d mu) i = BareDeg $ DegGet i mu 
