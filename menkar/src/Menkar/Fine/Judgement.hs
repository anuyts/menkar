module Menkar.Fine.Judgement where

import Menkar.Fine.Substitution
import Menkar.Fine.Syntax
import Data.Void
import Control.Exception.AssertFalse
import qualified Menkar.Raw.Syntax as Raw
import Data.Bifunctor
import Data.Maybe
import GHC.Generics
import Data.Functor.Identity
--import Data.Functor.Compose

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
  (:..) :: Ctx t mode modty v w -> Segment t t mode modty (Either v w) -> Ctx t mode modty (Maybe v) w
  {-| This is useful for affine DTT: you can extend a context with a shape variable up front, hide
      it right away and annotate some further variables as quantified over the new variable. -}
  (:^^) :: Segment t t mode modty w -> Ctx t mode modty v (Maybe w) -> Ctx t mode modty (Either () v) w
  {-| Context extended with siblings defined in a certain module. -}
  (:<...>) :: Ctx t mode modty v w -> ModuleRHS mode modty (Either v w) -> Ctx t mode modty (Identity v) w
  {-| Context divided by a modality. -}
  (:\\) :: ModedContramodality mode modty (Either v w) -> Ctx t mode modty v w -> Ctx t mode modty (Identity v) w
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
  Ctx t mode modty v w -> v -> Segment t t mode modty (Either v w)
getSegment CtxEmpty _ = unreachable
getSegment (gamma :.. segT) Nothing = bimap Just id <$> segT
getSegment (gamma :.. segT) (Just v) = bimap Just id <$> getSegment gamma v
getSegment (segT :^^ gamma) (Left ()) = Right <$> segT
getSegment (segT :^^ gamma) (Right v) = either
                                          (Left . Right)
                                          (fromMaybe (Left $ Left ()) . fmap Right)
                                          <$> getSegment gamma v
getSegment (segT :<...> _) (Identity v) = bimap Identity id <$> getSegment segT v
getSegment (kappa :\\ gamma) (Identity v) = bimap Identity id <$> todo

-------------------------------------------------------------

data Judgement (mode :: * -> *) (modty :: * -> *) (rel :: * -> *) where
  -- | @'JudType' gamma d tyT@ means @gamma |-{d} tyT type@
  JudType ::
    Ctx Type mode modty v Void ->
    mode v ->
    Type mode modty v ->
    Judgement mode modty rel
  JudTypeRel ::
    rel v ->
    Ctx (Pair3 Type) mode modty v Void ->
    mode v ->
    Pair3 Type mode modty v ->
    Judgement mode modty rel
  -- | @'JudTyping' gamma d t tyT@ means @gamma |-{d} t : tyT@.
  JudTyping ::
    Ctx Type mode modty v Void ->
    mode v ->
    Term mode modty v ->
    Type mode modty v ->
    Judgement mode modty rel
  JudTypingRel ::
    rel v ->
    Ctx (Pair3 Type) mode modty v Void ->
    mode v ->
    (Term mode modty v, Term mode modty v) ->
    Pair3 Type mode modty v ->
    Judgement mode modty rel
  -- | @'JudEta' gamma d t tyT@ means @gamma |-{d} t == some-eta-expansion : tyT@.
  JudEta ::
    Ctx Type mode modty v Void ->
    mode v -> 
    Term mode modty v ->
    Type mode modty v ->
    Judgement mode modty rel
  -- | @'JudSmartElim' gamma d t tyT es r@ means @gamma |-{d} (t : tyT) es ~> r@.
  JudSmartElim ::
    Ctx Type mode modty v Void ->
    mode v -> 
    Term mode modty v ->
    Type mode modty v ->
    [SmartEliminator mode modty v] ->
    Term mode modty v ->
    Judgement mode modty rel
  -- | @'JudResolve' gamma d t r tyT@ means @gamma |-{d} t ~> r : tyT@ where @t@ is a resolution call.
  JudResolve ::
    Ctx Type mode modty v Void ->
    mode v ->
    {- resolution call goes here -> -}
    Term mode modty v ->
    Type mode modty v ->
    Judgement mode modty rel
  -- JudAccuracy: "This term should be known up to that accuracy"
  -- JudReport: "This term is that goal and should be reported on" (maybe this is not a judgement, but something in the monad).

-------------------------------------------------------------

{-
peelTelescoped ::
  Ctx ty mode modty v ->
  Telescoped ty rhs mode modty v ->
  (forall w . (v -> w) -> Ctx ty mode modty w -> rhs mode modty w -> motive) ->
  motive
peelTelescoped gamma (Telescoped rhs) k = k id gamma rhs
peelTelescoped gamma (seg :|- thing) k =
  peelTelescoped (gamma :.. seg) thing (\ wkn' -> k (wkn' . Just))
-}
