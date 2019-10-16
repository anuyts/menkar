module Menkar.PrettyPrint.Aux.Context.Context where

import Menkar.System.Fine
import Menkar.Basic.Context
import Menkar.Fine.Context
import Menkar.Fine.Syntax
import qualified Menkar.Raw.Syntax as Raw

import Control.Exception.AssertFalse
import Data.Functor.Coerce

import GHC.Generics
import Data.Void
import Data.Kind
import Data.Proxy
import Data.Functor.Identity
import Data.Functor.Compose

-------------------------------------------------------------

-- The names "Sc*" do not make sense. It would be more sensible to use PP*, but whatever.

{-
data ModuleInScope (mode :: * -> *) (modty :: * -> *) (v :: *) =
  ModuleInScope {
    {-| Modality the currently defined value must be used by, in this module.
        This is the right adjoint to the contramodality by which the members of this module should be divided before use. -}
    moduleContramod :: ModedContramodality sys v,
    moduleContents :: ModuleRHS sys v
  }
  deriving (Functor, Foldable, Traversable, Generic1)
deriving instance (Functor mode, Functor modty, CanSwallow (Term sys) mode, CanSwallow (Term sys) modty) =>
  CanSwallow (Term sys) (ModuleInScope sys)
-}

newtype ScSegment (sys :: KSys) (v :: *) = ScSegment {scSegment'name :: Maybe Raw.Name}
  deriving (Functor, Traversable, Foldable, Generic1)
deriving anyclass instance (SysSyntax (Term sys) sys) =>
  CanSwallow (Term sys) (ScSegment sys)
segment2scSegment :: Segment ty sys v -> ScSegment sys v
segment2scSegment fineSeg = ScSegment $ _segment'name fineSeg

{-| Scoping context. Type arguments analogous to @'Ctx'@. -}
data ScCtx (sys :: KSys) (v :: *) where
  ScCtxEmpty :: ScCtx sys Void
  (::..) :: ScCtx sys v -> ScSegment sys v -> ScCtx sys (VarExt v)
  (::<...>) :: ScCtx sys v -> ModuleRHS sys v -> ScCtx sys (VarInModule v)
  (::\\) :: () -> ScCtx sys v -> ScCtx sys v
  ScCtxId :: ScCtx sys v -> ScCtx sys (Identity v)
  ScCtxComp :: ScCtx sys (f (g v)) -> ScCtx sys (Compose f g v)
infixl 3 ::.., ::<...>, ::\\
  
ctx2scCtx :: Ctx ty sys v -> ScCtx sys v
ctx2scCtx (CtxEmpty d) = ScCtxEmpty
ctx2scCtx (gamma :.. seg) = ctx2scCtx gamma ::.. segment2scSegment seg
ctx2scCtx (gamma :<...> modul) = ctx2scCtx gamma ::<...> modul
ctx2scCtx (dmu :\\ gamma) = () ::\\ ctx2scCtx gamma
ctx2scCtx (CtxId   gamma) = ScCtxId   $ ctx2scCtx gamma
ctx2scCtx (CtxComp gamma) = ScCtxComp $ ctx2scCtx gamma

scGetName :: ScCtx sys v -> v -> Maybe Raw.Name
scGetName ScCtxEmpty v = absurd v
scGetName (gamma ::.. seg) (VarWkn v) = scGetName gamma v
scGetName (gamma ::.. seg) (VarLast) = scSegment'name seg
scGetName (gamma ::<...> modul) (VarInModule v) = scGetName gamma v
scGetName (() ::\\ gamma) v = scGetName gamma v
scGetName (ScCtxId gamma) (Identity v) = scGetName gamma v
scGetName (ScCtxComp gamma) (Compose v) = scGetName gamma v

scListVariablesRev :: forall v sys . ScCtx sys v -> [v]
scListVariablesRev gamma = haveScDB gamma $ listAllRev @v
scListVariables :: forall v sys . ScCtx sys v -> [v]
scListVariables gamma = haveScDB gamma $ listAll @v

{-| @'mapTelescopedSc' f gamma <theta |- rhs>@ yields @<theta |- f wkn (gamma.theta) rhs>@ -}
mapTelescopedSc :: (Functor h, SysTrav sys, Functor (ty sys)) =>
  (forall w . (v -> w) -> ScCtx sys w -> rhs1 sys w -> h (rhs2 sys w)) ->
  (ScCtx sys v -> Telescoped ty rhs1 sys v -> h (Telescoped ty rhs2 sys v))
mapTelescopedSc f gamma (Telescoped rhs) = Telescoped <$> f id gamma rhs
mapTelescopedSc f gamma (seg :|- stuff) = (seg :|-) <$>
  mapTelescopedSc (f . (. VarWkn)) (gamma ::.. (segment2scSegment seg)) stuff
mapTelescopedSc f gamma (dmu :** stuff) = (dmu :**) <$>
  mapTelescopedSc f (() ::\\ gamma) stuff
{-| @'mapTelescopedScDB' f gamma <theta |- rhs>@ yields @<theta |- f wkn (gamma.theta) rhs>@ -}
mapTelescopedScDB :: (DeBruijnLevel v, Functor h, SysTrav sys, Functor (ty sys)) =>
  (forall w . DeBruijnLevel w => (v -> w) -> ScCtx sys w -> rhs1 sys w -> h (rhs2 sys w)) ->
  (ScCtx sys v -> Telescoped ty rhs1 sys v -> h (Telescoped ty rhs2 sys v))
mapTelescopedScDB f gamma (Telescoped rhs) = Telescoped <$> f id gamma rhs
mapTelescopedScDB f gamma (seg :|- stuff) = (seg :|-) <$>
  mapTelescopedScDB (f . (. VarWkn)) (gamma ::.. (segment2scSegment seg)) stuff
mapTelescopedScDB f gamma (dmu :** stuff) = (dmu :**) <$>
  mapTelescopedScDB f (() ::\\ gamma) stuff
  
haveScDB :: ScCtx sys v -> ((DeBruijnLevel v) => t) -> t
haveScDB (ScCtxEmpty) t = t
haveScDB (gamma ::.. _) t = haveScDB gamma t
haveScDB (gamma ::<...> _) t = haveScDB gamma t
haveScDB (_ ::\\ gamma) t = haveScDB gamma t
haveScDB (ScCtxId gamma) t = haveScDB gamma t
haveScDB (ScCtxComp gamma) t = haveScDB gamma t

_scCtx'sizeProxy :: ScCtx sys v -> Proxy v
_scCtx'sizeProxy gamma = Proxy
