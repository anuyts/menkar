
module Menkar.Fine.Context.Context where

import Menkar.Fine.Syntax
import Menkar.System.Fine
import Menkar.Basic.Context
import Control.Exception.AssertFalse
import qualified Menkar.Raw.Syntax as Raw

import Data.Functor.Coerce
import Data.Functor.Coyoneda.NF
import Control.DeepSeq.Redone

import Data.Void
import Data.Bifunctor
import Data.Maybe
import GHC.Generics
import Data.Functor.Identity
import Data.Functor.Compose
import Control.Lens
import Data.Proxy
import Data.Kind

{-| @'mapTelescoped' f gamma <theta |- rhs>@ yields @<theta |- f wkn (gamma.theta) rhs>@ -}
mapTelescoped :: (Functor h, SysTrav sys, Functor (ty sys)) =>
  (forall w . (v -> w) -> Ctx ty sys w -> rhs1 sys w -> h (rhs2 sys w)) ->
  (Ctx ty sys v -> Telescoped ty rhs1 sys v -> h (Telescoped ty rhs2 sys v))
mapTelescoped f gamma (Telescoped rhs) = Telescoped <$> f id gamma rhs
mapTelescoped f gamma (seg :|- stuff) = (seg :|-) <$>
  mapTelescoped (f . (. VarWkn)) (gamma :.. (seg)) stuff
mapTelescoped f gamma (dmu :** stuff) = (dmu :**) <$>
  mapTelescoped f ((dmu) :\\ gamma) stuff
{-| @'mapTelescopedDB' f gamma <theta |- rhs>@ yields @<theta |- f wkn (gamma.theta) rhs>@ -}
mapTelescopedDB :: (Functor h, SysTrav sys, Functor (ty sys), DeBruijnLevel v) =>
  (forall w . DeBruijnLevel w => (v -> w) -> Ctx ty sys w -> rhs1 sys w -> h (rhs2 sys w)) ->
  (Ctx ty sys v -> Telescoped ty rhs1 sys v -> h (Telescoped ty rhs2 sys v))
mapTelescopedDB f gamma (Telescoped rhs) = Telescoped <$> f id gamma rhs
mapTelescopedDB f gamma (seg :|- stuff) = (seg :|-) <$>
  mapTelescopedDB (f . (. VarWkn)) (gamma :.. (seg)) stuff
mapTelescopedDB f gamma (dmu :** stuff) = (dmu :**) <$>
  mapTelescopedDB f ((dmu) :\\ gamma) stuff

--------------------------

{- | @'Ctx' t sys v@ is the type of contexts with
     types of type @t@,
     modes of type @mode@,
     modalities of type @modty@,
     introducing @v@-many variables.
-}
data Ctx (t :: KSys -> * -> *) (sys :: KSys) (v :: *) where
  {-| Empty context. -}
  CtxEmpty :: Mode sys Void -> Ctx t sys Void
  {-| Extended context -}
  (:..) :: Ctx t sys v -> Segment t sys v -> Ctx t sys (VarExt v)
  {- {-| This is useful for affine DTT: you can extend a context with a shape variable up front, hide
      it right away and annotate some further variables as quantified over the new variable. -}
  (:^^) :: Segment t sys w -> Ctx t sys v (VarExt w) -> Ctx t sys (VarLeftExt v) w -}
  {-| Context extended with siblings defined in a certain module. -}
  (:<...>) :: Ctx t sys v -> ModuleRHS sys v -> Ctx t sys (VarInModule v)
  {-| Context divided by a modality. -}
  (:\\) :: ModalityTo sys v -> Ctx t sys v -> Ctx t sys v
  {-| Pleasing GHC -}
  CtxId :: Ctx t sys v -> Ctx t sys (Identity v)
  CtxComp :: Ctx t sys (f (g v)) -> Ctx t sys (Compose f g v)
  {-| Opaque context of a given mode. Used only for WHN.
      Necessary for whnormalizing meta dependencies, which should be enclosed in a LeftDivided.
  -}
  CtxOpaque :: DeBruijnLevel v => Mode sys v -> Ctx t sys v
--type role Ctx representational nominal nominal representational
instance (SysTrav sys, NFData_ (t sys)) => NFData (Ctx t sys v) where
  rnf (CtxEmpty d) = rnf_ d
  rnf (gamma :.. seg) = haveDB gamma $ rnf gamma `seq` rnf_ seg
  rnf (gamma :<...> modul) = haveDB gamma $ rnf gamma `seq` rnf_ modul
  rnf (mu :\\ gamma) = haveDB gamma $ rnf gamma `seq` rnf_ mu
  rnf (CtxId gamma) = haveDB gamma $ rnf gamma
  rnf (CtxComp gamma) = haveDB gamma $ rnf gamma
  rnf (CtxOpaque d) = rnf_ d
infixr 3 :\\
infixl 3 :.., :<...>

ctx'mode :: Multimode sys => Ctx ty sys v -> Coyoneda (Mode sys) v
ctx'mode (CtxEmpty d) = coy d
ctx'mode (gamma :.. seg) = VarWkn <$> ctx'mode gamma
ctx'mode (gamma :<...> modul) = VarInModule !<$> ctx'mode gamma
ctx'mode (dmu :\\ gamma) = coy $ _modalityTo'dom dmu
ctx'mode (CtxId gamma) = Identity !<$> ctx'mode gamma
ctx'mode (CtxComp gamma) = Compose !<$> ctx'mode gamma
ctx'mode (CtxOpaque d) = coy d

haveDB :: Ctx ty sys v -> ((DeBruijnLevel v) => t) -> t
haveDB (CtxEmpty d) t = t
haveDB (gamma :.. seg) t = haveDB gamma t
haveDB (gamma :<...> modul) t = haveDB gamma t
haveDB (dmu :\\ gamma) t = haveDB gamma t
haveDB (CtxId gamma) t = haveDB gamma t
haveDB (CtxComp gamma) t = haveDB gamma t
haveDB (CtxOpaque d) t = t

mapSegment :: (
    SysTrav sys,
    Functor (ty0 sys),
    Functor (ty1 sys),
    CanSwallow (Term sys) (ty0 sys),
    CanSwallow (Term sys) (ty1 sys)
  ) =>
  (forall sys' v' . ty0 sys' v' -> ty1 sys' v') ->
  Segment ty0 sys v -> Segment ty1 sys v
mapSegment f seg = over decl'content f seg
  
mapCtx :: (
    SysTrav sys,
    Functor (ty0 sys),
    Functor (ty1 sys),
    CanSwallow (Term sys) (ty0 sys),
    CanSwallow (Term sys) (ty1 sys)
  ) =>
  (forall sys' v' . ty0 sys' v' -> ty1 sys' v') ->
  Ctx ty0 sys v -> Ctx ty1 sys v
mapCtx f (CtxEmpty d) = CtxEmpty d
mapCtx f (gamma :.. seg) = mapCtx f gamma :.. mapSegment f seg
mapCtx f (gamma :<...> modul) = mapCtx f gamma :<...> modul
mapCtx f (dmu :\\ gamma) = dmu :\\ mapCtx f gamma
mapCtx f (CtxId gamma) = CtxId $ mapCtx f gamma
mapCtx f (CtxComp gamma) = CtxComp $ mapCtx f gamma
mapCtx f (CtxOpaque d) = CtxOpaque d

duplicateCtx :: (
    SysTrav sys,
    Functor (ty sys),
    CanSwallow (Term sys) (ty sys)
  ) =>
  Ctx ty sys v -> Ctx (Twice2 ty) sys v
duplicateCtx = mapCtx (\ty -> Twice2 ty ty)

fstCtx, sndCtx :: (
    SysTrav sys,
    Functor (ty sys),
    CanSwallow (Term sys) (ty sys)
  ) =>
  Ctx (Twice2 ty) sys v -> Ctx ty sys v
fstCtx = mapCtx (\(Twice2 ty1 ty2) -> ty1)
sndCtx = mapCtx (\(Twice2 ty1 ty2) -> ty2)

flipCtx :: (
    SysTrav sys,
    Functor (ty sys),
    CanSwallow (Term sys) (ty sys)
  ) =>
  Ctx (Twice2 ty) sys v -> Ctx (Twice2 ty) sys v
flipCtx = mapCtx (\(Twice2 ty1 ty2) -> Twice2 ty2 ty1)

ctx'sizeProxy :: Ctx ty sys v -> Proxy v
ctx'sizeProxy gamma = Proxy

{-
-- TODO: you need a left division here!
-- this can be further optimized by first returning `exists w . (segment w, w -> v)`
-- because `f <$> (g <$> x)` is much less efficient than `f . g <$> x`.
getSegment :: (Functor mode, Functor modty, Functor (t sys)) =>
  Ctx t sys v w -> v -> Segment t sys (VarOpenCtx v w)
getSegment CtxEmpty _ = unreachable
getSegment (gamma :.. segT) VarLast = bimap VarWkn id <$> segT
getSegment (gamma :.. segT) (VarWkn v) = bimap VarWkn id <$> getSegment gamma v
getSegment (segT :^^ gamma) VarFirst = VarBeforeCtx <$> segT
getSegment (segT :^^ gamma) (VarLeftWkn v) = (<$> getSegment gamma v) $
  \ u -> case u of
           VarBeforeCtx (VarWkn w) -> VarBeforeCtx w
           VarBeforeCtx VarLast -> VarFromCtx $ VarFirst
           VarFromCtx v -> VarFromCtx $ VarLeftWkn v
getSegment (segT :<...> _) (VarInModule v) = bimap VarInModule id <$> getSegment segT v
getSegment (kappa :\\ gamma) v = todo
-}

crispCtx :: (Multimode sys) => Ctx ty sys v -> Ctx ty sys v
crispCtx gamma = crispModalityTo (uncoy $ ctx'mode gamma) :\\ gamma
