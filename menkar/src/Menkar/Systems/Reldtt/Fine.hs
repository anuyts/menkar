module Menkar.Systems.Reldtt.Fine where

import Menkar.ID
import Menkar.Fine
import Menkar.System
import Menkar.Systems.Reldtt.Basic

import Control.Exception.AssertFalse
import Control.DeepSeq.Redone

import GHC.Generics
import Util
import Data.Functor.Compose
import Control.Lens

fst1 :: (a :*: b) c -> a c
fst1 (a :*: b) = a
snd1 :: (a :*: b) c -> b c
snd1 (a :*: b) = b

type instance Mode Reldtt = ReldttMode
type instance Modality Reldtt = ChainModty
type instance Degree Reldtt = ReldttDegree
type instance SysTerm Reldtt = ReldttSysTerm
type instance SysUniHSConstructor Reldtt = ReldttUniHSConstructor
type instance SysJudgement Reldtt = ReldttSysJudgement

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

--pattern BareMode :: ModeTerm v -> Term Reldtt v
pattern BareMode d = Expr2 (TermSys (SysTermMode (d :: ModeTerm v))) :: Term Reldtt v
--pattern BareFinMode :: ConstructorTerm Reldtt v -> Term Reldtt v
--pattern BareFinMode d = BareMode (ModeTermFinite (Expr2 (TermCons (d :: ConstructorTerm Reldtt v)))) :: Term Reldtt v
--pattern BareModeOmega :: Term Reldtt v
pattern BareModeOmega = BareMode ModeTermOmega :: Term Reldtt v
--pattern BareModty :: ModtyTerm v -> Term Reldtt v
pattern BareModty mu = Expr2 (TermSys (SysTermModty (mu :: ModtyTerm v))) :: Term Reldtt v
--pattern BareChainModty :: ChainModty v -> Term Reldtt v
pattern BareChainModty mu = BareModty (ModtyTermChain (mu :: ChainModty v)) :: Term Reldtt v
--pattern BareKnownModty :: KnownModty v -> Term Reldtt v
pattern BareKnownModty mu = BareChainModty (ChainModtyKnown (mu :: KnownModty v)) :: Term Reldtt v
--pattern BareDeg i :: ReldttDegree v -> Term Reldtt v
--pattern BareDeg i = Expr2 (TermSys (SysTermDeg (i :: ReldttDegree v))) :: Term Reldtt v
--pattern BareKnownDeg i :: KnownDeg -> Term Reldtt v
--pattern BareKnownDeg i = BareDeg (DegKnown (i :: KnownDeg)) :: Term Reldtt v
--pattern BareSysType :: ReldttUniHSConstructor v -> Type Reldtt v
pattern BareSysType systy = TypeHS (SysType (systy :: ReldttUniHSConstructor v)) :: Type Reldtt v
  --Type (Expr2 (TermSys (systy :: ReldttSysTerm v))) :: Type Reldtt v

data ModeTerm v = ModeTermZero | ModeTermSuc (Term Reldtt v) | ModeTermOmega
  deriving (Functor, Foldable, Traversable, Generic1, CanSwallow (Term Reldtt), NFData_)

newtype ReldttMode v = ReldttMode {getReldttMode :: Term Reldtt v}
  deriving (Functor, Foldable, Traversable, Generic1)
  deriving newtype (CanSwallow (Term Reldtt), NFData_)
deriving instance Generic (ReldttMode v)
deriving anyclass instance Wrapped (ReldttMode v)
--instance Wrapped (ReldttMode v) where
--  Unwrapped (ReldttMode v) = Term Reldtt v
--  _Wrapped f = dimap _ _

data ModtyTail v =
  TailEmpty |

  TailDisc   (Mode Reldtt v) {-^ Tail codomain, can be omega -} |
  --TailCodisc (Term Reldtt v) {-^ Tail codomain, can be omega -} |

  TailForget (Mode Reldtt v) {-^ Tail domain, can be omega -} |

  TailDiscForget   (Mode Reldtt v) {-^ Tail domain, can be omega -} (Mode Reldtt v) {-^ Tail codomain, can be omega -} |
  --TailCodiscForget (Term Reldtt v) {-^ Tail domain, can be omega -} (Term Reldtt v) {-^ Tail codomain, can be omega -} |
  TailCont (Mode Reldtt v) {-^ Tail domain and codomain, can be omega -} |

  TailProblem
  deriving (Functor, Foldable, Traversable, Generic1, CanSwallow (Term Reldtt), NFData_)

_snout'max :: ModtySnout -> KnownDeg
_snout'max (ModtySnout idom icod krevdegs) = case krevdegs of
  [] -> KnownDegEq
  krevdegs -> head krevdegs

data KnownModty v = KnownModty {_knownModty'snout :: ModtySnout, _knownModty'tail :: ModtyTail v}
  deriving (Functor, Foldable, Traversable, Generic1, CanSwallow (Term Reldtt), NFData_)

idKnownModty :: Mode Reldtt v -> KnownModty v
idKnownModty d = KnownModty (ModtySnout 0 0 []) (TailCont d)

forgetKnownModty :: Mode Reldtt v -> KnownModty v
forgetKnownModty dom = KnownModty (ModtySnout 0 0 []) (TailForget dom)

problemKnownModty :: KnownModty v
problemKnownModty = KnownModty (ModtySnout 0 0 []) TailProblem

addIntToMode :: Int -> Mode Reldtt v -> Mode Reldtt v
addIntToMode i d = d & _Wrapped' %~ nTimes i (BareMode . ModeTermSuc)

_knownModty'dom :: KnownModty v -> Mode Reldtt v
_knownModty'dom (KnownModty snout tail) = addIntToMode (_modtySnout'dom snout) (_modtyTail'dom tail)
  --_modtyTail'dom tail & _Wrapped' %~ nTimes (_modtySnout'dom snout) (BareMode . ModeTermSuc)
_knownModty'cod :: KnownModty v -> Mode Reldtt v
_knownModty'cod (KnownModty snout tail) = addIntToMode (_modtySnout'cod snout) (_modtyTail'cod tail)
  --_modtyTail'cod tail & _Wrapped' %~ nTimes (_modtySnout'cod snout) (BareMode . ModeTermSuc)

{-| The idea is that for whblocked ChainModtys, the whnormal ones are 'ChainModtyKnown' and 'ChainModtyLink',
    while the blocked ones are 'ChainModtyTerm'. However, 'ChainModtyKnwon' and 'ChainModtyLink' can still
    block on an unknown codomain, which may turn out to be 0, in which case the modality becomes the forgetful one.
-}
data ChainModty v =
  ChainModtyKnown (KnownModty v) |
  {-| It is an error to use this constructor on a term that is not whnormal (whblocked is not allowed).
      TODO FIXME: This invariant is not preserved under substitution!!!!! -}
  ChainModtyLink (KnownModty v) (Term Reldtt v) (ChainModty v) |
  {-| Reduces for ALL whnormal terms... (weird, I know) -}
  ChainModtyTerm
    (Mode Reldtt v) {-^ domain -}
    (Mode Reldtt v) {-^ codomain -}
    (Term Reldtt v) {-^ the modality -} |
  ChainModtyMeta
    (Mode Reldtt v) {-^ domain -}
    (Mode Reldtt v) {-^ codomain -}
    MetaID {-^ Meta's index -}
    (Dependencies Reldtt v) {-^ dependencies -} |
  ChainModtyAlreadyChecked
    (Mode Reldtt v) {-^ domain -}
    (Mode Reldtt v) {-^ codomain -}
    (ChainModty v) {-^ underlying chain modality -}
  deriving (Functor, Foldable, Traversable, Generic1, CanSwallow (Term Reldtt), NFData_)

wrapInChainModty :: Mode Reldtt v -> Mode Reldtt v -> Term Reldtt v -> ChainModty v
wrapInChainModty dom cod t = ChainModtyTerm dom cod t
  --ChainModtyLink (idKnownModty cod) t $ ChainModtyKnown $ idKnownModty dom

_chainModty'dom :: ChainModty v -> Mode Reldtt v
_chainModty'dom (ChainModtyKnown kmu) = _knownModty'dom $ kmu
_chainModty'dom (ChainModtyLink kmu termNu chainRho) = _chainModty'dom $ chainRho
_chainModty'dom (ChainModtyTerm dom cod tmu) = dom
_chainModty'dom (ChainModtyMeta dom cod meta depcies) = dom
_chainModty'dom (ChainModtyAlreadyChecked dom cod chmu) = dom
_chainModty'cod :: ChainModty v -> Mode Reldtt v
_chainModty'cod (ChainModtyKnown kmu) = _knownModty'cod $ kmu
_chainModty'cod (ChainModtyLink kmu termNu chainRho) = _knownModty'cod $ kmu
_chainModty'cod (ChainModtyTerm dom cod tmu) = cod
_chainModty'cod (ChainModtyMeta dom cod meta depcies) = cod
_chainModty'cod (ChainModtyAlreadyChecked dom cod chmu) = cod

extDisc :: ModtySnout -> ModtySnout
extDisc (ModtySnout kdom kcod []) = (ModtySnout kdom (kcod + 1) [KnownDegEq])
extDisc (ModtySnout kdom kcod (kdeg : krevdegs)) = (ModtySnout kdom (kcod + 1) (kdeg : kdeg : krevdegs))
--extCodisc :: ModtySnout -> ModtySnout
--extCodisc (ModtySnout kdom kcod krevdegs) = (ModtySnout kdom (kcod + 1) (KnownDegTop : krevdegs))
extForget :: ModtySnout -> ModtySnout
extForget (ModtySnout kdom kcod krevdegs) = (ModtySnout (kdom + 1) kcod krevdegs)
extCont :: ModtySnout -> ModtySnout
extCont (ModtySnout kdom kcod krevdegs) = ModtySnout (kdom + 1) (kcod + 1) (KnownDeg kdom : krevdegs)

forceDom :: forall v .
  ModtySnout ->
  ModtyTail v ->
  Int ->
  Mode Reldtt v ->
  Maybe (KnownModty v)
forceDom snoutOrig tailOrig snoutDomNew tailDomNew
  | _modtySnout'dom snoutOrig >  snoutDomNew = unreachable
  | _modtySnout'dom snoutOrig == snoutDomNew = Just $ KnownModty snoutOrig tailOrig
  | _modtySnout'dom snoutOrig <  snoutDomNew = case tailOrig of
      TailEmpty -> Nothing
      TailDisc   tailCod -> Nothing
      --TailCodisc tailCod -> Nothing
      TailForget tailDomOrig ->
        Just $ KnownModty (nTimes n extForget snoutOrig) (TailForget tailDomNew)
      TailDiscForget   tailDomOrig tailCod ->
        Just $ KnownModty (nTimes n extForget snoutOrig) (TailDiscForget tailDomNew tailCod)
      --TailCodiscForget tailDomOrig tailCod -> Just (nTimes n extForget snoutOrig, TailCodiscForget tailDomNew tailCod)
      TailCont tailModeOrig ->
        Just $ KnownModty (nTimes n extCont snoutOrig) (TailCont tailDomNew)
      TailProblem -> Nothing
  | otherwise = unreachable
    where n = snoutDomNew - _modtySnout'dom snoutOrig

forceCod :: forall v .
  ModtySnout ->
  ModtyTail v ->
  Int ->
  Mode Reldtt v ->
  Maybe (KnownModty v)
forceCod snoutOrig tailOrig snoutCodNew tailCodNew
  | _modtySnout'cod snoutOrig >  snoutCodNew = unreachable
  | _modtySnout'cod snoutOrig == snoutCodNew = Just $ KnownModty snoutOrig tailOrig
  | _modtySnout'cod snoutOrig <  snoutCodNew = case tailOrig of
      TailEmpty -> Nothing
      TailDisc   tailCodOrig ->
        Just $ KnownModty (nTimes n extDisc snoutOrig) (TailDisc tailCodNew)
      --TailCodisc tailCodOrig -> Just (nTimes n extCodisc snoutOrig, TailCodisc tailCodNew)
      TailForget tailDom -> Nothing
      TailDiscForget tailDom tailCodOrig ->
        Just $ KnownModty (nTimes n extDisc snoutOrig) (TailDiscForget tailDom tailCodNew)
      --TailCodiscForget tailDom tailCodOrig -> Just (nTimes n extCodisc snoutOrig, TailCodiscForget tailDom tailCodNew)
      TailCont tailModeOrig ->
        Just $ KnownModty (nTimes n extCont snoutOrig) (TailCont tailCodNew)
      TailProblem -> Nothing
  | otherwise = unreachable
    where n = snoutCodNew - _modtySnout'cod snoutOrig

_modtyTail'dom :: ModtyTail v -> Mode Reldtt v
_modtyTail'dom TailEmpty = ReldttMode $ BareMode $ ModeTermZero
_modtyTail'dom (TailDisc dcod) = ReldttMode $ BareMode $ ModeTermZero
--_modtyTail'dom (TailCodisc dcod) = BareFinMode $ ConsZero
_modtyTail'dom (TailForget ddom) = ddom
_modtyTail'dom (TailDiscForget ddom dcod) = ddom
--_modtyTail'dom (TailCodiscForget ddom dcod) = ddom
_modtyTail'dom (TailCont d) = d
_modtyTail'dom (TailProblem) = ReldttMode $ Expr2 $ TermProblem $ Expr2 $ TermWildcard

_modtyTail'cod :: ModtyTail v -> Mode Reldtt v
_modtyTail'cod TailEmpty = ReldttMode $ BareMode $ ModeTermZero
_modtyTail'cod (TailDisc dcod) = dcod
--_modtyTail'cod (TailCodisc dcod) = dcod
_modtyTail'cod (TailForget ddom) = ReldttMode $ BareMode $ ModeTermZero
_modtyTail'cod (TailDiscForget ddom dcod) = dcod
--_modtyTail'cod (TailCodiscForget ddom dcod) = dcod
_modtyTail'cod (TailCont d) = d
_modtyTail'cod (TailProblem) = ReldttMode $ Expr2 $ TermProblem $ Expr2 $ TermWildcard

data ModtyTerm v =
 --ModtyTerm ModtySnout (ModtyTail v) |
  ModtyTermChain (ChainModty v) |
  
  --{-| If @mu : d1 -> d2@ and @nu : d2 -> d3@, then the composite is @'ModtyTermComp' nu d2 mu@ -}
  --ModtyTermComp (Term Reldtt v) (Term Reldtt v) (Term Reldtt v) |
  {-| Only for prettypring.
      If @mu : d1 -> dcod@ and @rho : d2 -> dcod@, then @'ModtyTermDiv' rho mu@ denotes @rho \ mu : d1 -> d2@ -} 
  ModtyTermDiv (Term Reldtt v) (Term Reldtt v) |
  
  ModtyTermComp
    --(Mode Reldtt v) {-^ Codomain of result -}
    (ChainModty v) {-^ The postcomposite -}
    --(Mode Reldtt v) {-^ Intermediate mode -}
    (ChainModty v) {-^ The precomposite -}
    --(Mode Reldtt v) {-^ Domain of result -}
  |
  ModtyTermApproxLeftAdjointProj
    --(Mode Reldtt v) {-^ Domain of result -}
    --(Mode Reldtt v) {-^ Codomain of result -}
    (ChainModty v) {-^ The argument modality -} |
  
  {-| Only for prettyprinting. -} 
  ModtyTermUnavailable (Term Reldtt v) {-^ The domain, can be omega -} (Term Reldtt v) {-^ The codomain, can be omega -}
  deriving (Functor, Foldable, Traversable, Generic1, CanSwallow (Term Reldtt), NFData_)

_modtyTerm'dom :: ModtyTerm v -> Mode Reldtt v
_modtyTerm'dom (ModtyTermChain chmu) = _chainModty'dom chmu
_modtyTerm'dom (ModtyTermDiv _ _) = unreachable
_modtyTerm'dom (ModtyTermComp chmu2 chmu1) = _chainModty'dom chmu1
_modtyTerm'dom (ModtyTermApproxLeftAdjointProj chmu) = _chainModty'cod chmu
_modtyTerm'dom (ModtyTermUnavailable _ _) = unreachable

_modtyTerm'cod :: ModtyTerm v -> Mode Reldtt v
_modtyTerm'cod (ModtyTermChain chmu) = _chainModty'cod chmu
_modtyTerm'cod (ModtyTermDiv _ _) = unreachable
_modtyTerm'cod (ModtyTermComp chmu2 chmu1) = _chainModty'cod chmu2
_modtyTerm'cod (ModtyTermApproxLeftAdjointProj chmu) = _chainModty'dom chmu 
_modtyTerm'cod (ModtyTermUnavailable _ _) = unreachable

data ReldttDegree v =
  DegKnown
    (Mode Reldtt v) {-^ Degree's mode -}
    KnownDeg |
  DegGet
    (ReldttDegree v) {-^ Degree -}
    (ChainModty v) {-^ Modality -}
    --(Mode Reldtt v) {-^ Modality's domain; mode of the resulting degree. -}
    --(Mode Reldtt v) {-^ Modality's codomain; mode of the argument degree. -}
  deriving (Functor, Foldable, Traversable, Generic1, CanSwallow (Term Reldtt), NFData_)

_reldttDegree'mode :: ReldttDegree v -> Mode Reldtt v
_reldttDegree'mode (DegKnown d kdeg) = d
_reldttDegree'mode (DegGet deg chmu) = _chainModty'dom chmu

data ReldttSysTerm v =
  SysTermMode (ModeTerm v) |
  SysTermModty (ModtyTerm v)
  -- -- | This is a hack so that we can have metas for @'ChainModty'@
  --SysTermChainModtyInDisguise (ChainModty v)
  --SysTermDeg (ReldttDegree v)
  deriving (Functor, Foldable, Traversable, Generic1, CanSwallow (Term Reldtt), NFData_)

data ReldttUniHSConstructor v =
  {-| Type of modes. -}
  SysTypeMode |
  --{-| Type of degrees. -}
  --SysTypeDeg (ReldttMode v) {-^ Mode, can be omega. -} |
  {-| Type of modalities. -}
  SysTypeModty (ReldttMode v) {-^ Domain, can be omega -} (ReldttMode v) {-^ Codomain, can be omega -}
  deriving (Functor, Foldable, Traversable, Generic1, CanSwallow (Term Reldtt), NFData_)

data ReldttSysJudgement where
  deriving (Generic, NFData)

------------------------------

instance SysNF Reldtt where

instance SysTrav Reldtt where
  
instance SysSyntax (Term Reldtt) Reldtt

instance Multimode Reldtt where
  idMod d = ChainModtyKnown (idKnownModty d)
  compMod mu2 mu1 = ChainModtyTerm dom cod $ BareModty $ ModtyTermComp mu2 mu1
    where dom = _chainModty'dom mu1
          cod = _chainModty'cod mu2
    --ChainModtyLink (idKnownModty $ _chainModty'cod mu2) (BareChainModty mu2) $
    --ChainModtyLink (idKnownModty $ dmid) (BareChainModty mu1) $
    --ChainModtyKnown (idKnownModty $ _chainModty'dom mu1)
  divMod (ModedModality dom' cod' mu') (ModedModality dom cod mu) = wrapInChainModty dom dom' $
    BareModty (ModtyTermDiv (BareChainModty mu') (BareChainModty mu))
  divMod _ _ = unreachable
  crispMod d = ChainModtyKnown (KnownModty (ModtySnout 0 0 []) $ TailDisc d)
  dataMode = ReldttMode $ BareMode $ ModeTermZero
  approxLeftAdjointProj (ModedModality dom cod mu) = wrapInChainModty cod dom $
    BareModty (ModtyTermApproxLeftAdjointProj mu)
  approxLeftAdjointProj _ = unreachable
  _modality'dom = _chainModty'dom
  _modality'cod = _chainModty'cod

instance Degrees Reldtt where
  eqDeg d = DegKnown d KnownDegEq
  maybeTopDeg d = Just $ DegKnown d KnownDegTop
  divDeg mu i = DegGet i mu
  _degree'mode = _reldttDegree'mode

------------------------------
