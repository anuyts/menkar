
module Menkar.Fine.Context.Context where

import Menkar.Fine.Syntax
import Menkar.Basic.Context.Variable
import Menkar.Fine.Multimode
import Data.Void
import Control.Exception.AssertFalse
import qualified Menkar.Raw.Syntax as Raw
import Data.Bifunctor
import Data.Maybe
import GHC.Generics
import Data.Functor.Identity
import Control.Lens

{-| @'mapTelescopedSc' f gamma <theta |- rhs>@ yields @<theta |- f wkn (gamma.theta) rhs>@ -}
mapTelescoped :: (Functor h, Functor mode, Functor modty, Functor (ty mode modty)) =>
  (forall w . (v -> w) -> Ctx ty mode modty w Void -> rhs1 mode modty w -> h (rhs2 mode modty w)) ->
  (Ctx ty mode modty v Void -> Telescoped ty rhs1 mode modty v -> h (Telescoped ty rhs2 mode modty v))
mapTelescoped f gamma (Telescoped rhs) = Telescoped <$> f id gamma rhs
mapTelescoped f gamma (seg :|- stuff) = (seg :|-) <$>
  mapTelescoped (f . (. VarWkn)) (gamma :.. (VarFromCtx <$> seg)) stuff
mapTelescoped f gamma (dmu :** stuff) = (dmu :**) <$>
  mapTelescoped f ((VarFromCtx <$> dmu) :\\ gamma) stuff

--------------------------

{- | @'Ctx' t mode modty v w@ is the type of contexts with
     types of type @t@,
     modes of type @mode@,
     modalities of type @modty@,
     introducing @v@-many variables,
     and itself depending on variables of type @w@.
-}
data Ctx (t :: (* -> *) -> (* -> *) -> * -> *) (mode :: * -> *) (modty :: * -> *) (v :: *) (w :: *) where
  {-| Empty context. -}
  CtxEmpty :: mode w -> Ctx t mode modty Void w
  {-| Extended context -}
  (:..) :: Ctx t mode modty v w -> Segment t mode modty (VarOpenCtx v w) -> Ctx t mode modty (VarExt v) w
  {-| This is useful for affine DTT: you can extend a context with a shape variable up front, hide
      it right away and annotate some further variables as quantified over the new variable. -}
  (:^^) :: Segment t mode modty w -> Ctx t mode modty v (VarExt w) -> Ctx t mode modty (VarLeftExt v) w
  {-| Context extended with siblings defined in a certain module. -}
  (:<...>) :: Ctx t mode modty v w -> ModuleRHS mode modty (VarOpenCtx v w) -> Ctx t mode modty (VarInModule v) w
  {-| Context divided by a modality. -}
  (:\\) :: ModedModality mode modty (VarOpenCtx v w) -> Ctx t mode modty v w -> Ctx t mode modty v w
infixl 3 :.., :^^, :<...>, :\\
deriving instance (Functor mode, Functor modty, Functor (t mode modty)) => Functor (Ctx t mode modty v)
deriving instance (Foldable mode, Foldable modty, Foldable (t mode modty)) => Foldable (Ctx t mode modty v)
deriving instance (Traversable mode, Traversable modty, Traversable (t mode modty)) => Traversable (Ctx t mode modty v)
instance (
    Functor mode,
    Functor modty,
    Functor (t mode modty),
    CanSwallow (Term mode modty) mode,
    CanSwallow (Term mode modty) modty,
    CanSwallow (Term mode modty) (t mode modty)
  ) =>
    CanSwallow (Term mode modty) (Ctx t mode modty v) where
  swallow (CtxEmpty d) = CtxEmpty $ swallow d
  swallow (gamma :.. seg) = swallow gamma :.. swallow (fmap sequenceA seg)
  swallow (seg :^^ gamma) = swallow seg :^^ swallow (fmap sequenceA gamma)
  swallow (gamma :<...> modul) = swallow gamma :<...> swallow (fmap sequenceA modul)
  swallow (kappa :\\ gamma) = swallow (fmap sequenceA kappa) :\\ swallow gamma

ctx'mode :: Multimode mode modty => Ctx ty mode modty v w -> mode (VarOpenCtx v w)
ctx'mode (CtxEmpty d) = VarBeforeCtx <$> d
ctx'mode (gamma :.. seg) = bimap VarWkn id <$> ctx'mode gamma
ctx'mode (seg :^^ gamma) = varLeftEat <$> ctx'mode gamma
ctx'mode (gamma :<...> modul) = bimap VarInModule id <$> ctx'mode gamma
ctx'mode (dmu :\\ gamma) = modality'dom dmu

mapSegment :: (
    Functor mode,
    Functor modty,
    Functor (ty0 mode modty),
    Functor (ty1 mode modty),
    CanSwallow (Term mode modty) mode,
    CanSwallow (Term mode modty) modty,
    CanSwallow (Term mode modty) (ty0 mode modty),
    CanSwallow (Term mode modty) (ty1 mode modty)
  ) =>
  (forall mode' modty' v' . ty0 mode' modty' v' -> ty1 mode' modty' v') ->
  Segment ty0 mode modty v -> Segment ty1 mode modty v
mapSegment f seg = over decl'content f seg
  
mapCtx :: (
    Functor mode,
    Functor modty,
    Functor (ty0 mode modty),
    Functor (ty1 mode modty),
    CanSwallow (Term mode modty) mode,
    CanSwallow (Term mode modty) modty,
    CanSwallow (Term mode modty) (ty0 mode modty),
    CanSwallow (Term mode modty) (ty1 mode modty)
  ) =>
  (forall mode' modty' v' . ty0 mode' modty' v' -> ty1 mode' modty' v') ->
  Ctx ty0 mode modty v w -> Ctx ty1 mode modty v w
mapCtx f (CtxEmpty d) = CtxEmpty d
mapCtx f (gamma :.. seg) = mapCtx f gamma :.. mapSegment f seg
mapCtx f (seg :^^ gamma) = mapSegment f seg :^^ mapCtx f gamma
mapCtx f (gamma :<...> modul) = mapCtx f gamma :<...> modul
mapCtx f (dmu :\\ gamma) = dmu :\\ mapCtx f gamma

duplicateCtx :: (
    Functor mode,
    Functor modty,
    Functor (ty mode modty),
    CanSwallow (Term mode modty) mode,
    CanSwallow (Term mode modty) modty,
    CanSwallow (Term mode modty) (ty mode modty)
  ) =>
  Ctx ty mode modty v w -> Ctx (Pair3 ty) mode modty v w
duplicateCtx = mapCtx (\ty -> Pair3 ty ty)

{-
-- TODO: you need a left division here!
-- this can be further optimized by first returning `exists w . (segment w, w -> v)`
-- because `f <$> (g <$> x)` is much less efficient than `f . g <$> x`.
getSegment :: (Functor mode, Functor modty, Functor (t mode modty)) =>
  Ctx t mode modty v w -> v -> Segment t mode modty (VarOpenCtx v w)
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
