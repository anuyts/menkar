module Menkar.Syntax.Context where

import Menkar.Syntax.Composable
import Menkar.Syntax.Syntax
import Data.Void
import Control.Exception.AssertFalse

data Ctx (mobj :: * -> *) (mhom :: * -> *) (v :: *) where
  CtxEmpty :: Ctx mobj mhom Void
  (:..) :: Ctx mobj mhom v -> Segment mobj mhom v -> Ctx mobj mhom (Maybe v)
  {-| This is useful for affine DTT: you can extend a context with a shape variable up front, hide
      it right away and annotate some further variables as quantified over the new variable. -}
  (:^^) :: Segment mobj mhom Void -> Ctx mobj mhom v -> Ctx mobj mhom (Either () v)

-- this can be further optimized by first returning `exists w . (segment w, w -> v)`
-- because `f <$> (g <$> x)` is much less efficient than `f . g <$> x`.
getSegment :: (Functor mobj, Functor mhom) => Ctx mobj mhom v -> v -> Segment mobj mhom v
getSegment CtxEmpty _ = unreachable
getSegment (gamma :.. segT) Nothing = Just <$> segT
getSegment (gamma :.. segT) (Just v) = Just <$> getSegment gamma v
getSegment (segT :^^ gamma) (Left ()) = absurd <$> segT
getSegment (segT :^^ gamma) (Right v) = Right <$> getSegment gamma v
