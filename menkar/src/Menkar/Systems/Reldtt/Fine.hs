module Menkar.Systems.Reldtt.Fine where

import Menkar.Fine
import Menkar.System

import Control.Exception.AssertFalse

import GHC.Generics
import Util
import Data.Functor.Compose
import Control.Lens

fst1 :: (a :*: b) c -> a c
fst1 (a :*: b) = a
snd1 :: (a :*: b) c -> b c
snd1 (a :*: b) = b

data Reldtt :: KSys where

type instance Mode Reldtt = Term Reldtt
type instance Modality Reldtt = ChainModty
type instance Degree Reldtt = DegTerm
type instance SysTerm Reldtt = ReldttSysTerm
type instance SysUniHSConstructor Reldtt = ReldttUniHSConstructor

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
--pattern BareDeg i :: DegTerm v -> Term Reldtt v
--pattern BareDeg i = Expr2 (TermSys (SysTermDeg (i :: DegTerm v))) :: Term Reldtt v
--pattern BareKnownDeg i :: KnownDeg -> Term Reldtt v
--pattern BareKnownDeg i = BareDeg (DegKnown (i :: KnownDeg)) :: Term Reldtt v
--pattern BareSysType :: ReldttUniHSConstructor v -> Type Reldtt v
pattern BareSysType systy = TypeHS (SysType (systy :: ReldttUniHSConstructor v)) :: Type Reldtt v
  --Type (Expr2 (TermSys (systy :: ReldttSysTerm v))) :: Type Reldtt v

data ModeTerm v = ModeTermZero | ModeTermSuc (Term Reldtt v) | ModeTermOmega
  deriving (Functor, Foldable, Traversable, Generic1, CanSwallow (Term Reldtt))

data KnownDeg =
  KnownDegEq |
  KnownDeg Int |
  KnownDegTop |
  KnownDegOmega {-^ Only allowed in infinite modes. -} |
  KnownDegProblem
  deriving (Eq, Ord)

-- | It is an error to create a nonsensical @'ModtySnout'@.
data ModtySnout = ModtySnout
  {_modtySnout'dom :: Int,
   _modtySnout'cod :: Int,
   {-| Degrees in REVERSE ORDER. -}
   _modtySnout'degreesReversed :: [KnownDeg]
  }
data ModtyTail v =
  TailEmpty |

  TailDisc   (Term Reldtt v) {-^ Tail codomain, can be omega -} |
  --TailCodisc (Term Reldtt v) {-^ Tail codomain, can be omega -} |

  TailForget (Term Reldtt v) {-^ Tail domain, can be omega -} |

  TailDiscForget   (Term Reldtt v) {-^ Tail domain, can be omega -} (Term Reldtt v) {-^ Tail codomain, can be omega -} |
  --TailCodiscForget (Term Reldtt v) {-^ Tail domain, can be omega -} (Term Reldtt v) {-^ Tail codomain, can be omega -} |
  TailCont (Term Reldtt v) {-^ Tail domain and codomain, can be omega -} |

  TailProblem
  deriving (Functor, Foldable, Traversable, Generic1, CanSwallow (Term Reldtt))

_snout'max :: ModtySnout -> KnownDeg
_snout'max (ModtySnout idom icod krevdegs) = case krevdegs of
  [] -> KnownDegEq
  krevdegs -> last krevdegs

{-
numberfyOmegasForDomainlessTail :: ModtySnout -> ModtySnout
numberfyOmegasForDomainlessTail mu@(ModtySnout idom icod krevdegs) = ModtySnout idom icod $ krevdegs <&> \ case
  KnownDegOmega -> KnownDeg $ idom - 1
  kdeg -> kdeg
-}

{-| Precondition: Tails start at the same point and have the same (co)domain.
    Precondition for correct result: The snouts are leq. -} 
relTail_ :: ModRel -> ModtySnout -> ModtySnout -> ModtyTail v -> ModtyTail v -> Bool
relTail_ rel _ _ TailProblem _ = False
relTail_ rel _ _ _ TailProblem = False
relTail_ rel _ _ TailEmpty TailEmpty = True
relTail_ rel _ _ TailEmpty _ = unreachable
relTail_ rel _ _ _ TailEmpty = unreachable
relTail_ rel _ _ (TailDisc dcod) (TailDisc dcod') = True
relTail_ rel _ _ (TailDisc dcod) (TailForget ddom') = unreachable
relTail_ rel _ _ (TailDisc dcod) (TailDiscForget ddom' dcod') = unreachable
relTail_ rel _ _ (TailDisc dcod) (TailCont d') = unreachable
relTail_ rel _ _ (TailForget ddom) (TailDisc dcod') = unreachable
relTail_ rel _ _ (TailForget ddom) (TailForget ddom') = True
relTail_ rel _ _ (TailForget ddom) (TailDiscForget ddom' dcod') = unreachable
relTail_ rel _ _ (TailForget ddom) (TailCont d') = unreachable
relTail_ rel _ _ (TailDiscForget ddom dcod) (TailDisc dcod') = unreachable
relTail_ rel _ _ (TailDiscForget ddom dcod) (TailForget ddom') = unreachable
relTail_ rel _ _ (TailDiscForget ddom dcod) (TailDiscForget ddom' dcod') = True
relTail_ rel _ _ (TailDiscForget ddom dcod) (TailCont d') = case rel of
  ModLeq -> True
  ModEq -> False
  -- The only way that @ModLeq@ can be false, is when the left snout ends in Top, but then
  -- if the snouts are leq, then so does the right one, so you can't have TailCont.
relTail_ rel _ _ (TailCont d) (TailDisc dcod') = unreachable
relTail_ rel _ _ (TailCont d) (TailForget ddom') = unreachable
relTail_ rel _ snoutR (TailCont d) (TailDiscForget ddom' dcod') = case rel of
  ModEq -> False
  ModLeq -> case _modtySnout'degreesReversed snoutR of
    [] -> False
    (KnownDegTop : _) -> True
    _ -> False
relTail_ rel _ _ (TailCont d) (TailCont d') = True

relTail :: ModRel -> KnownModty v -> KnownModty v -> Bool
relTail rel (KnownModty snoutL tailL) (KnownModty snoutR tailR) = relTail_ rel snoutL snoutR tailL tailR

data KnownModty v = KnownModty {_knownModty'snout :: ModtySnout, _knownModty'tail :: ModtyTail v}
  deriving (Functor, Foldable, Traversable, Generic1, CanSwallow (Term Reldtt))

idKnownModty :: Term Reldtt v -> KnownModty v
idKnownModty d = KnownModty (ModtySnout 0 0 []) (TailCont d)

problemKnownModty :: KnownModty v
problemKnownModty = KnownModty (ModtySnout 0 0 []) TailProblem

_knownModty'dom :: KnownModty v -> Term Reldtt v
_knownModty'dom (KnownModty snout tail) = nTimes (_modtySnout'dom snout) (BareMode . ModeTermSuc) $ _modtyTail'dom tail
_knownModty'cod :: KnownModty v -> Term Reldtt v
_knownModty'cod (KnownModty snout tail) = nTimes (_modtySnout'cod snout) (BareMode . ModeTermSuc) $ _modtyTail'cod tail

data ChainModty v =
  ChainModtyKnown (KnownModty v) |
  ChainModtyLink (KnownModty v) (Term Reldtt v) (ChainModty v) |
  ChainModtyMeta
    (Term Reldtt v) {-^ domain -}
    (Term Reldtt v) {-^ codomain -}
    Int {-^ meta index -}
    (Compose [] (Term Reldtt) v) {-^ dependencies -}
  deriving (Functor, Foldable, Traversable, Generic1, CanSwallow (Term Reldtt))

wrapInChainModty :: Term Reldtt v -> Term Reldtt v -> Term Reldtt v -> ChainModty v
wrapInChainModty ddom dcod t = ChainModtyLink (idKnownModty dcod) t $ ChainModtyKnown $ idKnownModty ddom

_chainModty'cod :: ChainModty v -> Term Reldtt v
_chainModty'cod (ChainModtyKnown kmu) = _knownModty'cod $ kmu
_chainModty'cod (ChainModtyLink kmu termNu chainRho) = _knownModty'cod $ kmu
_chainModty'cod (ChainModtyMeta dom cod meta depcies) = cod
_chainModty'dom :: ChainModty v -> Term Reldtt v
_chainModty'dom (ChainModtyKnown kmu) = _knownModty'dom $ kmu
_chainModty'dom (ChainModtyLink kmu termNu chainRho) = _chainModty'dom $ chainRho
_chainModty'dom (ChainModtyMeta dom cod meta depcies) = dom

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
  Term Reldtt v ->
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
  Term Reldtt v ->
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

_modtyTail'dom :: ModtyTail v -> Term Reldtt v
_modtyTail'dom TailEmpty = BareMode $ ModeTermZero
_modtyTail'dom (TailDisc dcod) = BareMode $ ModeTermZero
--_modtyTail'dom (TailCodisc dcod) = BareFinMode $ ConsZero
_modtyTail'dom (TailForget ddom) = ddom
_modtyTail'dom (TailDiscForget ddom dcod) = ddom
--_modtyTail'dom (TailCodiscForget ddom dcod) = ddom
_modtyTail'dom (TailCont d) = d
_modtyTail'dom (TailProblem) = Expr2 $ TermProblem $ BareMode $ ModeTermZero

_modtyTail'cod :: ModtyTail v -> Term Reldtt v
_modtyTail'cod TailEmpty = BareMode $ ModeTermZero
_modtyTail'cod (TailDisc dcod) = dcod
--_modtyTail'cod (TailCodisc dcod) = dcod
_modtyTail'cod (TailForget ddom) = BareMode $ ModeTermZero
_modtyTail'cod (TailDiscForget ddom dcod) = dcod
--_modtyTail'cod (TailCodiscForget ddom dcod) = dcod
_modtyTail'cod (TailCont d) = d
_modtyTail'cod (TailProblem) = Expr2 $ TermProblem $ BareMode $ ModeTermZero

data ModtyTerm v =
 --ModtyTerm ModtySnout (ModtyTail v) |
  ModtyTermChain (ChainModty v) |
  
  --{-| If @mu : d1 -> d2@ and @nu : d2 -> d3@, then the composite is @'ModtyTermComp' nu d2 mu@ -}
  --ModtyTermComp (Term Reldtt v) (Term Reldtt v) (Term Reldtt v) |
  {-| Only for prettypring.
      If @mu : d1 -> dcod@ and @rho : d2 -> dcod@, then @'ModtyTermDiv' rho mu@ denotes @rho \ mu : d1 -> d2@ -} 
  ModtyTermDiv (Term Reldtt v) (Term Reldtt v) |
  ModtyTermApproxLeftAdjointProj
    (Term Reldtt v) {-^ Domain of result -}
    (Term Reldtt v) {-^ Codomain of result -}
    (Term Reldtt v) {-^ The argument modality -} |
  
  {-| Only for prettyprinting. -} 
  ModtyTermUnavailable (Term Reldtt v) {-^ The domain, can be omega -} (Term Reldtt v) {-^ The codomain, can be omega -}
  deriving (Functor, Foldable, Traversable, Generic1, CanSwallow (Term Reldtt))

data DegTerm v =
  DegKnown KnownDeg |
  DegGet
    (DegTerm v) {-^ Degree -}
    (Term Reldtt v) {-^ Modality -}
    (Term Reldtt v) {-^ Modality's domain; mode of the resulting degree. -}
    (Term Reldtt v) {-^ Modality's codomain; mode of the argument degree. -}
  deriving (Functor, Foldable, Traversable, Generic1, CanSwallow (Term Reldtt))

data ReldttSysTerm v =
  SysTermMode (ModeTerm v) |
  SysTermModty (ModtyTerm v) |
   -- | This is a hack so that we can have metas for @'ChainModty'@
  SysTermChainModtyInDisguise (ChainModty v)
  --SysTermDeg (DegTerm v)
  deriving (Functor, Foldable, Traversable, Generic1, CanSwallow (Term Reldtt))

data ReldttUniHSConstructor v =
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
  idMod d = ChainModtyKnown (idKnownModty d)
  compMod mu2 dmid mu1 =
    ChainModtyLink (idKnownModty $ _chainModty'cod mu2) (BareChainModty mu2) $
    ChainModtyLink (idKnownModty $ dmid) (BareChainModty mu1) $
    ChainModtyKnown (idKnownModty $ _chainModty'dom mu1)
  divMod (ModedModality d' mu') (ModedModality d mu) =
    ChainModtyLink (idKnownModty d') (BareModty (ModtyTermDiv (BareChainModty mu') (BareChainModty mu))) $
    ChainModtyKnown (idKnownModty d)
  crispMod d = ChainModtyKnown (KnownModty (ModtySnout 0 0 []) $ TailDisc d)
  dataMode = BareMode $ ModeTermZero
  approxLeftAdjointProj (ModedModality d mu) dcod =
    ChainModtyLink (idKnownModty d) (BareModty (ModtyTermApproxLeftAdjointProj dcod d $ BareChainModty mu)) $
    ChainModtyKnown (idKnownModty dcod)

instance Degrees Reldtt where
  eqDeg = DegKnown $ KnownDegEq
  maybeTopDeg = Just $ DegKnown $ KnownDegTop
  divDeg (ModedModality ddom mu) (ModedDegree dcod i) = DegGet i (BareChainModty mu) ddom dcod

------------------------------
