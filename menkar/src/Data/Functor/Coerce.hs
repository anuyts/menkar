module Data.Functor.Coerce where

import Data.Coerce
import Unsafe.Coerce

-- | If we have quantified constraints, and can make types like Ctx representational in v, then we can make this work.
(!<$>) :: forall f a b . (Functor f, Coercible a b) => (a -> b) -> f a -> f b
--h !<$> fa = h <$> fa
h !<$> fa = unsafeCoerce fa
{-
(!<$>) :: forall f a b . (Functor f, Coercible a b, forall x y . Coercible x y => Coercible (f x) (f y)) =>
  (a -> b) -> f a -> f b
h !<$> fa = coerce fa
-}

infixl 4 !<$>

fmapCoe :: forall f a b . (Functor f, Coercible a b) => (a -> b) -> f a -> f b
fmapCoe = (!<$>)
--fmapCoe :: forall f a b . (Functor f, Coercible a b, forall x y . Coercible x y => Coercible (f x) (f y)) =>
--  (a -> b) -> f a -> f b
