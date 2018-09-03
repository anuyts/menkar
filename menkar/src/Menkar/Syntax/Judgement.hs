module Menkar.Syntax.Judgement where

import Menkar.Syntax.Composable
import Menkar.Syntax.Syntax
import Data.Void
import Control.Exception.AssertFalse

data Ctx (t :: (* -> *) -> (* -> *) -> * -> *) (mode :: * -> *) (modty :: * -> *) (v :: *) where
  CtxEmpty :: Ctx t mode modty Void
  (:..) :: Ctx t mode modty v -> Segment t mode modty v -> Ctx t mode modty (Maybe v)
  {-| This is useful for affine DTT: you can extend a context with a shape variable up front, hide
      it right away and annotate some further variables as quantified over the new variable. -}
  (:^^) :: Segment t mode modty Void -> Ctx t mode modty v -> Ctx t mode modty (Either () v)

-- this can be further optimized by first returning `exists w . (segment w, w -> v)`
-- because `f <$> (g <$> x)` is much less efficient than `f . g <$> x`.
getSegment :: (Functor mode, Functor modty, Functor (t mode modty)) => Ctx t mode modty v -> v -> Segment t mode modty v
getSegment CtxEmpty _ = unreachable
getSegment (gamma :.. segT) Nothing = Just <$> segT
getSegment (gamma :.. segT) (Just v) = Just <$> getSegment gamma v
getSegment (segT :^^ gamma) (Left ()) = absurd <$> segT
getSegment (segT :^^ gamma) (Right v) = Right <$> getSegment gamma v

-------------------------------------------------------------

data Judgement (mode :: * -> *) (modty :: * -> *) (rel :: * -> *) where
  -- | @'JudType' gamma d tyT@ means @gamma |-{d} tyT type@
  JudType ::
    Ctx Type mode modty v ->
    mode v ->
    Type mode modty v ->
    Judgement mode modty rel
  JudTypeRel ::
    rel v ->
    Ctx (Pair3 Type) mode modty v ->
    mode v ->
    Pair3 Type mode modty v ->
    Judgement mode modty rel
  -- | @'JudTyping' gamma d t tyT@ means @gamma |-{d} t : tyT@.
  JudTyping ::
    Ctx Type mode modty v ->
    mode v ->
    Term mode modty v ->
    Type mode modty v ->
    Judgement mode modty rel
  JudTypingRel ::
    rel v ->
    Ctx (Pair3 Type) mode modty v ->
    mode v ->
    (Term mode modty v, Term mode modty v) ->
    Pair3 Type mode modty v ->
    Judgement mode modty rel
  -- | @'JudEta' gamma d t tyT@ means @gamma |-{d} t == some-eta-expansion : tyT@.
  JudEta ::
    Ctx Type mode modty v ->
    mode v -> 
    Term mode modty v ->
    Type mode modty v ->
    Judgement mode modty rel
  -- | @'JudSmartElim' gamma d t tyT es r@ means @gamma |-{d} (t : tyT) es ~> r@.
  JudSmartElim ::
    Ctx Type mode modty v ->
    mode v -> 
    Term mode modty v ->
    Type mode modty v ->
    [SmartEliminator mode modty v] ->
    Term mode modty v ->
    Judgement mode modty rel
  -- | @'JudResolve' gamma d t r tyT@ means @gamma |-{d} t ~> r : tyT@ where @t@ is a resolution call.
  JudResolve ::
    Ctx Type mode modty v ->
    mode v ->
    {- resolution call goes here -> -}
    Term mode modty v ->
    Type mode modty v ->
    Judgement mode modty rel
