
module Menkar.Fine.Context.Context where

import Menkar.Fine.Syntax
import Menkar.Basic.Context
import Menkar.Fine.Multimode
import Control.Exception.AssertFalse
import qualified Menkar.Raw.Syntax as Raw

import Data.Void
import Data.Bifunctor
import Data.Maybe
import GHC.Generics
import Data.Functor.Identity
import Control.Lens
import Data.Proxy
import Data.Kind

{-| @'mapTelescoped' f gamma <theta |- rhs>@ yields @<theta |- f wkn (gamma.theta) rhs>@ -}
mapTelescoped :: (Functor h, SysTrav sys, Functor (ty sys)) =>
  (forall w . (v -> w) -> Ctx ty sys w Void -> rhs1 sys w -> h (rhs2 sys w)) ->
  (Ctx ty sys v Void -> Telescoped ty rhs1 sys v -> h (Telescoped ty rhs2 sys v))
mapTelescoped f gamma (Telescoped rhs) = Telescoped <$> f id gamma rhs
mapTelescoped f gamma (seg :|- stuff) = (seg :|-) <$>
  mapTelescoped (f . (. VarWkn)) (gamma :.. (VarFromCtx <$> seg)) stuff
mapTelescoped f gamma (dmu :** stuff) = (dmu :**) <$>
  mapTelescoped f ((VarFromCtx <$> dmu) :\\ gamma) stuff
{-| @'mapTelescopedDB' f gamma <theta |- rhs>@ yields @<theta |- f wkn (gamma.theta) rhs>@ -}
mapTelescopedDB :: (Functor h, SysTrav sys, Functor (ty sys), DeBruijnLevel v) =>
  (forall w . DeBruijnLevel w => (v -> w) -> Ctx ty sys w Void -> rhs1 sys w -> h (rhs2 sys w)) ->
  (Ctx ty sys v Void -> Telescoped ty rhs1 sys v -> h (Telescoped ty rhs2 sys v))
mapTelescopedDB f gamma (Telescoped rhs) = Telescoped <$> f id gamma rhs
mapTelescopedDB f gamma (seg :|- stuff) = (seg :|-) <$>
  mapTelescopedDB (f . (. VarWkn)) (gamma :.. (VarFromCtx <$> seg)) stuff
mapTelescopedDB f gamma (dmu :** stuff) = (dmu :**) <$>
  mapTelescopedDB f ((VarFromCtx <$> dmu) :\\ gamma) stuff

--------------------------

{- | @'Ctx' t sys v w@ is the type of contexts with
     types of type @t@,
     modes of type @mode@,
     modalities of type @modty@,
     introducing @v@-many variables,
     and itself depending on variables of type @w@.
-}
data Ctx (t :: KSys -> * -> *) (sys :: KSys) (v :: *) (w :: *) where
  {-| Empty context. -}
  CtxEmpty :: Mode sys w -> Ctx t sys Void w
  {-| Extended context -}
  (:..) :: Ctx t sys v w -> Segment t sys (VarOpenCtx v w) -> Ctx t sys (VarExt v) w
  {-| This is useful for affine DTT: you can extend a context with a shape variable up front, hide
      it right away and annotate some further variables as quantified over the new variable. -}
  (:^^) :: Segment t sys w -> Ctx t sys v (VarExt w) -> Ctx t sys (VarLeftExt v) w
  {-| Context extended with siblings defined in a certain module. -}
  (:<...>) :: Ctx t sys v w -> ModuleRHS sys (VarOpenCtx v w) -> Ctx t sys (VarInModule v) w
  {-| Context divided by a modality. -}
  (:\\) :: ModedModality sys (VarOpenCtx v w) -> Ctx t sys v w -> Ctx t sys v w
infixl 3 :.., :^^, :<...>, :\\
deriving instance (SysTrav sys, Functor (t sys)) => Functor (Ctx t sys v)
deriving instance (SysTrav sys, Foldable (t sys)) => Foldable (Ctx t sys v)
deriving instance (SysTrav sys, Traversable (t sys)) => Traversable (Ctx t sys v)
instance (
    SysSyntax (Term sys) sys,
    Functor (t sys),
    CanSwallow (Term sys) (t sys)
  ) =>
    CanSwallow (Term sys) (Ctx t sys v) where
  swallow (CtxEmpty d) = CtxEmpty $ swallow d
  swallow (gamma :.. seg) = swallow gamma :.. swallow (fmap sequenceA seg)
  swallow (seg :^^ gamma) = swallow seg :^^ swallow (fmap sequenceA gamma)
  swallow (gamma :<...> modul) = swallow gamma :<...> swallow (fmap sequenceA modul)
  swallow (kappa :\\ gamma) = swallow (fmap sequenceA kappa) :\\ swallow gamma

ctx'mode :: Multimode sys => Ctx ty sys v w -> Mode sys (VarOpenCtx v w)
ctx'mode (CtxEmpty d) = VarBeforeCtx <$> d
ctx'mode (gamma :.. seg) = bimap VarWkn id <$> ctx'mode gamma
ctx'mode (seg :^^ gamma) = varLeftEat <$> ctx'mode gamma
ctx'mode (gamma :<...> modul) = bimap VarInModule id <$> ctx'mode gamma
ctx'mode (dmu :\\ gamma) = modality'dom dmu

haveDB :: Ctx ty sys v w -> ((DeBruijnLevel v) => t) -> t
haveDB (CtxEmpty d) t = t
haveDB (gamma :.. seg) t = haveDB gamma t
haveDB (seg :^^ gamma) t = todo
haveDB (gamma :<...> modul) t = haveDB gamma t
haveDB (dmu :\\ gamma) t = haveDB gamma t

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
  Ctx ty0 sys v w -> Ctx ty1 sys v w
mapCtx f (CtxEmpty d) = CtxEmpty d
mapCtx f (gamma :.. seg) = mapCtx f gamma :.. mapSegment f seg
mapCtx f (seg :^^ gamma) = mapSegment f seg :^^ mapCtx f gamma
mapCtx f (gamma :<...> modul) = mapCtx f gamma :<...> modul
mapCtx f (dmu :\\ gamma) = dmu :\\ mapCtx f gamma

duplicateCtx :: (
    SysTrav sys,
    Functor (ty sys),
    CanSwallow (Term sys) (ty sys)
  ) =>
  Ctx ty sys v w -> Ctx (Twice2 ty) sys v w
duplicateCtx = mapCtx (\ty -> Twice2 ty ty)

fstCtx, sndCtx :: (
    SysTrav sys,
    Functor (ty sys),
    CanSwallow (Term sys) (ty sys)
  ) =>
  Ctx (Twice2 ty) sys v w -> Ctx ty sys v w
fstCtx = mapCtx (\(Twice2 ty1 ty2) -> ty1)
sndCtx = mapCtx (\(Twice2 ty1 ty2) -> ty2)

flipCtx :: (
    SysTrav sys,
    Functor (ty sys),
    CanSwallow (Term sys) (ty sys)
  ) =>
  Ctx (Twice2 ty) sys v w -> Ctx (Twice2 ty) sys v w
flipCtx = mapCtx (\(Twice2 ty1 ty2) -> Twice2 ty2 ty1)

ctx'sizeProxy :: Ctx ty sys v w -> Proxy v
ctx'sizeProxy gamma = Proxy

externalizeCtx :: (SysTrav sys, Functor (ty sys)) => Ctx ty sys v Void -> Ctx ty sys v v
externalizeCtx (CtxEmpty d) = CtxEmpty d
externalizeCtx (gamma :.. seg) =
  VarWkn <$> externalizeCtx gamma :.. VarBeforeCtx . VarWkn . unVarFromCtx <$> seg
externalizeCtx (seg :^^ gamma) = todo
externalizeCtx (gamma :<...> modul) =
  VarInModule <$> externalizeCtx gamma :<...> VarBeforeCtx . VarInModule . unVarFromCtx <$> modul
externalizeCtx (dmu :\\ gamma) = externalizeVar <$> dmu :\\ externalizeCtx gamma

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
