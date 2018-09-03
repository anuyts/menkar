module Menkar.Syntax.Judgement where

import Menkar.Syntax.Composable
import Menkar.Syntax.Syntax
import Data.Void
import Control.Exception.AssertFalse

data Ctx (t :: (* -> *) -> (* -> *) -> * -> *) (mode :: * -> *) (mhom :: * -> *) (v :: *) where
  CtxEmpty :: Ctx t mode mhom Void
  (:..) :: Ctx t mode mhom v -> Segment t mode mhom v -> Ctx t mode mhom (Maybe v)
  {-| This is useful for affine DTT: you can extend a context with a shape variable up front, hide
      it right away and annotate some further variables as quantified over the new variable. -}
  (:^^) :: Segment t mode mhom Void -> Ctx t mode mhom v -> Ctx t mode mhom (Either () v)

-- this can be further optimized by first returning `exists w . (segment w, w -> v)`
-- because `f <$> (g <$> x)` is much less efficient than `f . g <$> x`.
getSegment :: (Functor mode, Functor mhom, Functor (t mode mhom)) => Ctx t mode mhom v -> v -> Segment t mode mhom v
getSegment CtxEmpty _ = unreachable
getSegment (gamma :.. segT) Nothing = Just <$> segT
getSegment (gamma :.. segT) (Just v) = Just <$> getSegment gamma v
getSegment (segT :^^ gamma) (Left ()) = absurd <$> segT
getSegment (segT :^^ gamma) (Right v) = Right <$> getSegment gamma v

-------------------------------------------------------------

data Judgement (mode :: * -> *) (mhom :: * -> *) where
  -- | @'JudType' gamma d tyT@ means @gamma |-{d} tyT type@
  JudType :: Ctx Type mode mhom v -> mode v -> Type mode mhom v -> Judgement mode mhom
  
  -- | @'JudTyping' gamma d t tyT@ means @gamma |-{d} t : tyT@.
  JudTyping :: Ctx Type mode mhom v -> mode v -> Term mode mhom v -> Type mode mhom v -> Judgement mode mhom
  -- | @'JudSmartElim' gamma d t tyT es r@ means @gamma |-{d} (t : tyT) es ~> r@.
  JudSmartElim ::
    Ctx Type mode mhom v ->
    mode v -> 
    Term mode mhom v ->
    Type mode mhom v ->
    [SmartEliminator mode mhom v] ->
    Term mode mhom v ->
    Judgement mode mhom
  -- | @'JudEta' gamma d t tyT@ means @gamma |-{d} t == some-eta-expansion : tyT@.
  JudEta ::
    Ctx Type mode mhom v ->
    mode v -> 
    Term mode mhom v ->
    Type mode mhom v ->
    Judgement mode mhom
