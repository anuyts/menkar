
{-# OPTIONS_GHC -Wno-incomplete-patterns #-}

module Menkar.Fine.Context where

import Menkar.Fine.Substitution
import Menkar.Fine.Syntax
import Menkar.Fine.Context.Variable
import Data.Void
import Control.Exception.AssertFalse
import qualified Menkar.Raw.Syntax as Raw
import Data.Bifunctor
import Data.Maybe
import GHC.Generics
import Data.Functor.Identity

-------------------------------------------------------------

{-
data ModuleInScope (mode :: * -> *) (modty :: * -> *) (v :: *) =
  ModuleInScope {
    {-| Modality the currently defined value must be used by, in this module.
        This is the right adjoint to the contramodality by which the members of this module should be divided before use. -}
    moduleContramod :: ModedContramodality mode modty v,
    moduleContents :: ModuleRHS mode modty v
  }
  deriving (Functor, Foldable, Traversable, Generic1)
deriving instance (Functor mode, Functor modty, CanSwallow (Term mode modty) mode, CanSwallow (Term mode modty) modty) =>
  CanSwallow (Term mode modty) (ModuleInScope mode modty)
-}

newtype ScSegment (mode :: * -> *) (modty :: * -> *) (v :: *) = ScSegment {scSegment'name :: Maybe Raw.Name}
  deriving (Functor, Traversable, Foldable, Generic1)
deriving instance (Functor mode, Functor modty, CanSwallow (Term mode modty) mode, CanSwallow (Term mode modty) modty) =>
  CanSwallow (Term mode modty) (ScSegment mode modty)
segment2scSegment :: Segment ty mode modty v -> ScSegment mode modty v
segment2scSegment fineSeg = ScSegment $ _segment'name fineSeg

{-| Scoping context. Type arguments analogous to @'Ctx'@. -}
data ScCtx (mode :: * -> *) (modty :: * -> *) (v :: *) (w :: *) where
  ScCtxEmpty :: ScCtx mode modty Void w
  (::..) :: ScCtx mode modty v w -> ScSegment mode modty (VarOpenCtx v w) -> ScCtx mode modty (VarExt v) w
  (::^^) :: ScSegment mode modty w -> ScCtx mode modty v (VarExt w) -> ScCtx mode modty (VarLeftExt v) w
  (::<...>) :: ScCtx mode modty v w -> ModuleRHS mode modty (VarOpenCtx v w) -> ScCtx mode modty (VarInModule v) w
  (::\\) :: () -> ScCtx mode modty v w -> ScCtx mode modty (VarDiv v) w
deriving instance (Functor mode, Functor modty) => Functor (ScCtx mode modty v)
deriving instance (Foldable mode, Foldable modty) => Foldable (ScCtx mode modty v)
deriving instance (Traversable mode, Traversable modty) => Traversable (ScCtx mode modty v)
instance (
    Functor mode,
    Functor modty,
    CanSwallow (Term mode modty) mode,
    CanSwallow (Term mode modty) modty
  ) =>
    CanSwallow (Term mode modty) (ScCtx mode modty v) where
  swallow ScCtxEmpty = ScCtxEmpty
  swallow (gamma ::.. seg) = swallow gamma ::.. swallow (fmap sequenceA seg)
  swallow (seg ::^^ gamma) = swallow seg ::^^ swallow (fmap sequenceA gamma)
  swallow (gamma ::<...> modul) = swallow gamma ::<...> swallow (fmap sequenceA modul)
  swallow (() ::\\ gamma) = () ::\\ swallow gamma
infixl 3 ::.., ::^^, ::<...>, ::\\

scGetName :: ScCtx mode modty v w -> v -> Maybe Raw.Name
scGetName ScCtxEmpty v = absurd v
scGetName (gamma ::.. seg) (VarWkn v) = scGetName gamma v
scGetName (gamma ::.. seg) (VarLast) = scSegment'name seg
scGetName (seg ::^^ gamma) (VarLeftWkn v) = scGetName gamma v
scGetName (seg ::^^ gamma) (VarFirst) = scSegment'name seg
scGetName (gamma ::<...> modul) (VarInModule v) = scGetName gamma v
scGetName (() ::\\ gamma) (VarDiv v) = scGetName gamma v

{- | @'Ctx' t mode modty v w@ is the type of contexts with
     types of type @t@,
     modes of type @mode@,
     modalities of type @modty@,
     introducing @v@-many variables,
     and itself depending on variables of type @w@.
-}
data Ctx (t :: (* -> *) -> (* -> *) -> * -> *) (mode :: * -> *) (modty :: * -> *) (v :: *) (w :: *) where
  {-| Empty context. -}
  CtxEmpty :: Ctx t mode modty Void w
  {-| Extended context -}
  (:..) :: Ctx t mode modty v w -> Segment t mode modty (VarOpenCtx v w) -> Ctx t mode modty (VarExt v) w
  {-| This is useful for affine DTT: you can extend a context with a shape variable up front, hide
      it right away and annotate some further variables as quantified over the new variable. -}
  (:^^) :: Segment t mode modty w -> Ctx t mode modty v (VarExt w) -> Ctx t mode modty (VarLeftExt v) w
  {-| Context extended with siblings defined in a certain module. -}
  (:<...>) :: Ctx t mode modty v w -> ModuleRHS mode modty (VarOpenCtx v w) -> Ctx t mode modty (VarInModule v) w
  {-| Context divided by a modality. -}
  (:\\) :: ModedContramodality mode modty (VarOpenCtx v w) -> Ctx t mode modty v w -> Ctx t mode modty (VarDiv v) w
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
  swallow CtxEmpty = CtxEmpty
  swallow (gamma :.. seg) = swallow gamma :.. swallow (fmap sequenceA seg)
  swallow (seg :^^ gamma) = swallow seg :^^ swallow (fmap sequenceA gamma)
  swallow (gamma :<...> modul) = swallow gamma :<...> swallow (fmap sequenceA modul)
  swallow (kappa :\\ gamma) = swallow (fmap sequenceA kappa) :\\ swallow gamma

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
getSegment (kappa :\\ gamma) (VarDiv v) = bimap VarDiv id <$> todo
