module Data.Functor.Coerce where

import Data.Coerce

(!<$>) :: forall f a b . (Functor f, Coercible a b, Coercible (f a) (f b)) => (a -> b) -> f a -> f b
h !<$> fa = coerce fa
