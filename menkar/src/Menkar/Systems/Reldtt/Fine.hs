module Menkar.Systems.Reldtt.Fine where

import Menkar.Fine
import Menkar.System

import Control.Exception.AssertFalse

import GHC.Generics
import Util

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
pattern BareSysType systy = Type (Expr2 (TermSys systy))

data ModeTerm v = ModeTermFinite (Term Reldtt v) | ModeTermOmega
  deriving (Functor, Foldable, Traversable, Generic1, CanSwallow (Term Reldtt))

data KnownDeg = KnownDegEq | KnownDeg Int | KnownDegTop
data KnownModty = KnownModty
  {_knownModty'dom :: Int,
   _knownModty'cod :: Int,
   {-| Degrees in REVERSE ORDER. -}
   _knownModty'degreesReversed :: [KnownDeg]
  }
data ModtyTail v =
  TailEmpty |

  TailDisc   (Term Reldtt v) {-^ Tail codomain, can be omega -} |
  --TailCodisc (Term Reldtt v) {-^ Tail codomain, can be omega -} |

  TailForget (Term Reldtt v) {-^ Tail domain, can be omega -} |

  TailDiscForget   (Term Reldtt v) {-^ Tail domain, can be omega -} (Term Reldtt v) {-^ Tail codomain, can be omega -} |
  --TailCodiscForget (Term Reldtt v) {-^ Tail domain, can be omega -} (Term Reldtt v) {-^ Tail codomain, can be omega -} |
  TailCont (Term Reldtt v) {-^ Tail domain and codomain, can be omega -}
  deriving (Functor, Foldable, Traversable, Generic1, CanSwallow (Term Reldtt))

extDisc :: KnownModty -> KnownModty
extDisc (KnownModty kdom kcod []) = (KnownModty kdom (kcod + 1) [KnownDegEq])
extDisc (KnownModty kdom kcod (kdeg : krevdegs)) = (KnownModty kdom (kcod + 1) (kdeg : kdeg : krevdegs))
--extCodisc :: KnownModty -> KnownModty
--extCodisc (KnownModty kdom kcod krevdegs) = (KnownModty kdom (kcod + 1) (KnownDegTop : krevdegs))
extForget :: KnownModty -> KnownModty
extForget (KnownModty kdom kcod krevdegs) = (KnownModty (kdom + 1) kcod krevdegs)
extCont :: KnownModty -> KnownModty
extCont (KnownModty kdom kcod krevdegs) = KnownModty (kdom + 1) (kcod + 1) (KnownDeg kdom : krevdegs)

forceDom :: forall v .
  KnownModty ->
  ModtyTail v ->
  Int ->
  Term Reldtt v ->
  Maybe (KnownModty, ModtyTail v)
forceDom snoutOrig tailOrig snoutDomNew tailDomNew
  | _knownModty'dom snoutOrig >  snoutDomNew = unreachable
  | _knownModty'dom snoutOrig == snoutDomNew = Just (snoutOrig, tailOrig)
  | _knownModty'dom snoutOrig <  snoutDomNew = case tailOrig of
      TailEmpty -> Nothing
      TailDisc   tailCod -> Nothing
      --TailCodisc tailCod -> Nothing
      TailForget tailDomOrig -> Just (nTimes n extForget snoutOrig, TailForget tailDomNew)
      TailDiscForget   tailDomOrig tailCod -> Just (nTimes n extForget snoutOrig, TailDiscForget   tailDomNew tailCod)
      --TailCodiscForget tailDomOrig tailCod -> Just (nTimes n extForget snoutOrig, TailCodiscForget tailDomNew tailCod)
      TailCont tailModeOrig -> Just (nTimes n extCont snoutOrig, TailCont tailDomNew)
  | otherwise = unreachable
    where n = snoutDomNew - _knownModty'dom snoutOrig

forceCod :: forall v .
  KnownModty ->
  ModtyTail v ->
  Int ->
  Term Reldtt v ->
  Maybe (KnownModty, ModtyTail v)
forceCod snoutOrig tailOrig snoutCodNew tailCodNew
  | _knownModty'cod snoutOrig >  snoutCodNew = unreachable
  | _knownModty'cod snoutOrig == snoutCodNew = Just (snoutOrig, tailOrig)
  | _knownModty'cod snoutOrig <  snoutCodNew = case tailOrig of
      TailEmpty -> Nothing
      TailDisc   tailCodOrig -> Just (nTimes n extDisc   snoutOrig, TailDisc   tailCodNew)
      --TailCodisc tailCodOrig -> Just (nTimes n extCodisc snoutOrig, TailCodisc tailCodNew)
      TailForget tailDom -> Nothing
      TailDiscForget   tailDom tailCodOrig -> Just (nTimes n extDisc   snoutOrig, TailDiscForget   tailDom tailCodNew)
      --TailCodiscForget tailDom tailCodOrig -> Just (nTimes n extCodisc snoutOrig, TailCodiscForget tailDom tailCodNew)
      TailCont tailModeOrig -> Just (nTimes n extCont snoutOrig, TailCont tailCodNew)
  | otherwise = unreachable
    where n = snoutCodNew - _knownModty'cod snoutOrig

_modtyTail'dom :: ModtyTail v -> Term Reldtt v
_modtyTail'dom TailEmpty = BareFinMode $ ConsZero
_modtyTail'dom (TailDisc dcod) = BareFinMode $ ConsZero
--_modtyTail'dom (TailCodisc dcod) = BareFinMode $ ConsZero
_modtyTail'dom (TailForget ddom) = ddom
_modtyTail'dom (TailDiscForget ddom dcod) = ddom
--_modtyTail'dom (TailCodiscForget ddom dcod) = ddom
_modtyTail'dom (TailCont d) = d

_modtyTail'cod :: ModtyTail v -> Term Reldtt v
_modtyTail'cod TailEmpty = BareFinMode $ ConsZero
_modtyTail'cod (TailDisc dcod) = dcod
--_modtyTail'cod (TailCodisc dcod) = dcod
_modtyTail'cod (TailForget ddom) = BareFinMode $ ConsZero
_modtyTail'cod (TailDiscForget ddom dcod) = dcod
--_modtyTail'cod (TailCodiscForget ddom dcod) = dcod
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
