module Menkar.PrettyPrint.Aux.Context.Context where

import Menkar.Basic.Context
import Menkar.Fine.Context
import Menkar.Fine.Syntax
import qualified Menkar.Raw.Syntax as Raw

import Control.Exception.AssertFalse

import GHC.Generics
import Data.Void
import Data.Kind

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
deriving instance (SysSyntax (Term sys) sys) =>
  CanSwallow (Term sys) (ScSegment sys)
segment2scSegment :: Segment ty sys v -> ScSegment sys v
segment2scSegment fineSeg = ScSegment $ _segment'name fineSeg

{-| Scoping context. Type arguments analogous to @'Ctx'@. -}
data ScCtx (sys :: KSys) (v :: *) (w :: *) where
  ScCtxEmpty :: ScCtx sys Void w
  (::..) :: ScCtx sys v w -> ScSegment sys (VarOpenCtx v w) -> ScCtx sys (VarExt v) w
  (::^^) :: ScSegment sys w -> ScCtx sys v (VarExt w) -> ScCtx sys (VarLeftExt v) w
  (::<...>) :: ScCtx sys v w -> ModuleRHS sys (VarOpenCtx v w) -> ScCtx sys (VarInModule v) w
  (::\\) :: () -> ScCtx sys v w -> ScCtx sys v w
deriving instance (SysTrav sys) => Functor (ScCtx sys v)
deriving instance (SysTrav sys) => Foldable (ScCtx sys v)
deriving instance (SysTrav sys) => Traversable (ScCtx sys v)
instance (SysSyntax (Term sys) sys) =>
    CanSwallow (Term sys) (ScCtx sys v) where
  swallow ScCtxEmpty = ScCtxEmpty
  swallow (gamma ::.. seg) = swallow gamma ::.. swallow (fmap sequenceA seg)
  swallow (seg ::^^ gamma) = swallow seg ::^^ swallow (fmap sequenceA gamma)
  swallow (gamma ::<...> modul) = swallow gamma ::<...> swallow (fmap sequenceA modul)
  swallow (() ::\\ gamma) = () ::\\ swallow gamma
infixl 3 ::.., ::^^, ::<...>, ::\\
ctx2scCtx :: Ctx ty sys v w -> ScCtx sys v w
ctx2scCtx (CtxEmpty d) = ScCtxEmpty
ctx2scCtx (gamma :.. seg) = ctx2scCtx gamma ::.. segment2scSegment seg
ctx2scCtx (seg :^^ gamma) = segment2scSegment seg ::^^ ctx2scCtx gamma
ctx2scCtx (gamma :<...> modul) = ctx2scCtx gamma ::<...> modul
ctx2scCtx (dmu :\\ gamma) = () ::\\ ctx2scCtx gamma

scGetName :: ScCtx sys v w -> v -> Maybe Raw.Name
scGetName ScCtxEmpty v = absurd v
scGetName (gamma ::.. seg) (VarWkn v) = scGetName gamma v
scGetName (gamma ::.. seg) (VarLast) = scSegment'name seg
scGetName (seg ::^^ gamma) (VarLeftWkn v) = scGetName gamma v
scGetName (seg ::^^ gamma) (VarFirst) = scSegment'name seg
scGetName (gamma ::<...> modul) (VarInModule v) = scGetName gamma v
scGetName (() ::\\ gamma) v = scGetName gamma v

scListVariablesRev :: ScCtx sys v w -> [v]
scListVariablesRev ScCtxEmpty = []
scListVariablesRev (gamma ::.. _) = VarLast : (VarWkn <$> scListVariablesRev gamma)
scListVariablesRev (_ ::^^ gamma) = (VarLeftWkn <$> scListVariablesRev gamma) ++ [VarFirst]
scListVariablesRev (gamma ::<...> _) = VarInModule <$> scListVariablesRev gamma
scListVariablesRev (() ::\\ gamma) = scListVariablesRev gamma
scListVariables :: ScCtx sys v w -> [v]
scListVariables = reverse . scListVariablesRev

{-| @'mapTelescopedSc' f gamma <theta |- rhs>@ yields @<theta |- f wkn (gamma.theta) rhs>@ -}
mapTelescopedSc :: (Functor h, SysTrav sys, Functor (ty sys)) =>
  (forall w . (v -> w) -> ScCtx sys w Void -> rhs1 sys w -> h (rhs2 sys w)) ->
  (ScCtx sys v Void -> Telescoped ty rhs1 sys v -> h (Telescoped ty rhs2 sys v))
mapTelescopedSc f gamma (Telescoped rhs) = Telescoped <$> f id gamma rhs
mapTelescopedSc f gamma (seg :|- stuff) = (seg :|-) <$>
  mapTelescopedSc (f . (. VarWkn)) (gamma ::.. (VarFromCtx <$> segment2scSegment seg)) stuff
mapTelescopedSc f gamma (dmu :** stuff) = (dmu :**) <$>
  mapTelescopedSc f (() ::\\ gamma) stuff
{-| @'mapTelescopedScDB' f gamma <theta |- rhs>@ yields @<theta |- f wkn (gamma.theta) rhs>@ -}
mapTelescopedScDB :: (DeBruijnLevel v, Functor h, SysTrav sys, Functor (ty sys)) =>
  (forall w . DeBruijnLevel w => (v -> w) -> ScCtx sys w Void -> rhs1 sys w -> h (rhs2 sys w)) ->
  (ScCtx sys v Void -> Telescoped ty rhs1 sys v -> h (Telescoped ty rhs2 sys v))
mapTelescopedScDB f gamma (Telescoped rhs) = Telescoped <$> f id gamma rhs
mapTelescopedScDB f gamma (seg :|- stuff) = (seg :|-) <$>
  mapTelescopedScDB (f . (. VarWkn)) (gamma ::.. (VarFromCtx <$> segment2scSegment seg)) stuff
mapTelescopedScDB f gamma (dmu :** stuff) = (dmu :**) <$>
  mapTelescopedScDB f (() ::\\ gamma) stuff
  
haveScDB :: ScCtx sys v Void -> ((DeBruijnLevel v) => t) -> t
haveScDB (ScCtxEmpty) t = t
haveScDB (gamma ::.. _) t = haveScDB gamma t
haveScDB (_ ::^^ gamma) t = todo
haveScDB (gamma ::<...> _) t = haveScDB gamma t
haveScDB (_ ::\\ gamma) t = haveScDB gamma t
