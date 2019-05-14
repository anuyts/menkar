module Data.Functor.Coerce where

import Data.Coerce

-- | If we have quantified constraints, then we can make this work.
(!<$>) :: forall f a b . (Functor f, Coercible a b) => (a -> b) -> f a -> f b
h !<$> fa = h <$> fa
