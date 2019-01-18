module Menkar.PrettyPrint.Aux.Context.Context where

import Menkar.Basic.Context
import Menkar.Fine.Context
import Menkar.Fine.Syntax
import qualified Menkar.Raw.Syntax as Raw

import Control.Exception.AssertFalse

import GHC.Generics
import Data.Void

-------------------------------------------------------------

-- The names "Sc*" do not make sense. It would be more sensible to use PP*, but whatever.

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
  (::\\) :: () -> ScCtx mode modty v w -> ScCtx mode modty v w
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
ctx2scCtx :: Ctx ty mode modty v w -> ScCtx mode modty v w
ctx2scCtx (CtxEmpty d) = ScCtxEmpty
ctx2scCtx (gamma :.. seg) = ctx2scCtx gamma ::.. segment2scSegment seg
ctx2scCtx (seg :^^ gamma) = segment2scSegment seg ::^^ ctx2scCtx gamma
ctx2scCtx (gamma :<...> modul) = ctx2scCtx gamma ::<...> modul
ctx2scCtx (dmu :\\ gamma) = () ::\\ ctx2scCtx gamma

scGetName :: ScCtx mode modty v w -> v -> Maybe Raw.Name
scGetName ScCtxEmpty v = absurd v
scGetName (gamma ::.. seg) (VarWkn v) = scGetName gamma v
scGetName (gamma ::.. seg) (VarLast) = scSegment'name seg
scGetName (seg ::^^ gamma) (VarLeftWkn v) = scGetName gamma v
scGetName (seg ::^^ gamma) (VarFirst) = scSegment'name seg
scGetName (gamma ::<...> modul) (VarInModule v) = scGetName gamma v
scGetName (() ::\\ gamma) v = scGetName gamma v

scListVariablesRev :: ScCtx mode modty v w -> [v]
scListVariablesRev ScCtxEmpty = []
scListVariablesRev (gamma ::.. _) = VarLast : (VarWkn <$> scListVariablesRev gamma)
scListVariablesRev (_ ::^^ gamma) = (VarLeftWkn <$> scListVariablesRev gamma) ++ [VarFirst]
scListVariablesRev (gamma ::<...> _) = VarInModule <$> scListVariablesRev gamma
scListVariablesRev (() ::\\ gamma) = scListVariablesRev gamma
scListVariables :: ScCtx mode modty v w -> [v]
scListVariables = reverse . scListVariablesRev

{-| @'mapTelescopedSc' f gamma <theta |- rhs>@ yields @<theta |- f wkn (gamma.theta) rhs>@ -}
mapTelescopedSc :: (Functor h, Functor mode, Functor modty, Functor (ty mode modty)) =>
  (forall w . (v -> w) -> ScCtx mode modty w Void -> rhs1 mode modty w -> h (rhs2 mode modty w)) ->
  (ScCtx mode modty v Void -> Telescoped ty rhs1 mode modty v -> h (Telescoped ty rhs2 mode modty v))
mapTelescopedSc f gamma (Telescoped rhs) = Telescoped <$> f id gamma rhs
mapTelescopedSc f gamma (seg :|- stuff) = (seg :|-) <$>
  mapTelescopedSc (f . (. VarWkn)) (gamma ::.. (VarFromCtx <$> segment2scSegment seg)) stuff
mapTelescopedSc f gamma (dmu :** stuff) = (dmu :**) <$>
  mapTelescopedSc f (() ::\\ gamma) stuff
{-| @'mapTelescopedScDB' f gamma <theta |- rhs>@ yields @<theta |- f wkn (gamma.theta) rhs>@ -}
mapTelescopedScDB :: (DeBruijnLevel v, Functor h, Functor mode, Functor modty, Functor (ty mode modty)) =>
  (forall w . DeBruijnLevel w => (v -> w) -> ScCtx mode modty w Void -> rhs1 mode modty w -> h (rhs2 mode modty w)) ->
  (ScCtx mode modty v Void -> Telescoped ty rhs1 mode modty v -> h (Telescoped ty rhs2 mode modty v))
mapTelescopedScDB f gamma (Telescoped rhs) = Telescoped <$> f id gamma rhs
mapTelescopedScDB f gamma (seg :|- stuff) = (seg :|-) <$>
  mapTelescopedScDB (f . (. VarWkn)) (gamma ::.. (VarFromCtx <$> segment2scSegment seg)) stuff
mapTelescopedScDB f gamma (dmu :** stuff) = (dmu :**) <$>
  mapTelescopedScDB f (() ::\\ gamma) stuff
  
haveScDB :: ScCtx mode modty v Void -> ((DeBruijnLevel v) => t) -> t
haveScDB (ScCtxEmpty) t = t
haveScDB (gamma ::.. _) t = haveScDB gamma t
haveScDB (_ ::^^ gamma) t = todo
haveScDB (gamma ::<...> _) t = haveScDB gamma t
haveScDB (_ ::\\ gamma) t = haveScDB gamma t
