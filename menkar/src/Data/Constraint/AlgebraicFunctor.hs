{-# LANGUAGE AllowAmbiguousTypes, UndecidableInstances #-}

module Data.Constraint.AlgebraicFunctor where

import Data.Functor.Functor1
import Data.Constraint.Image

import GHC.Generics
import Data.Constraint.Trivial
import Data.Functor
import Data.Functor.Compose
import Data.Coerce
import Unsafe.Coerce

class AlgebraicFunctor c f where
  algmap :: forall x y . (c x, c y) => (x -> y) -> f x -> f y
  default algmap :: forall x y . (Generic1 f, AlgebraicFunctor c (Rep1 f), c x, c y) => (x -> y) -> f x -> f y
  algmap f = to1 . algmap @c f . from1

(<@>) :: forall c f x y . (AlgebraicFunctor c f, c x, c y) => (x -> y) -> f x -> f y
(<@>) = algmap @c

algmapCoe :: forall c f x y . (AlgebraicFunctor c f, c x, c y, Coercible x y) => (x -> y) -> f x -> f y
algmapCoe f = unsafeCoerce
(!<@>) :: forall c f x y . (AlgebraicFunctor c f, c x, c y, Coercible x y) => (x -> y) -> f x -> f y
(!<@>) = algmapCoe @c

--instance Functor f => AlgebraicFunctor Unconstrained f where
--  algmap = fmap

----------------------------------

instance AlgebraicFunctor c V1 where
  algmap f v = case v of {}

instance AlgebraicFunctor c U1 where
  algmap f U1 = U1

instance AlgebraicFunctor c Par1 where
  algmap f (Par1 x) = Par1 $ f x

instance (AlgebraicFunctor c f) => AlgebraicFunctor c (Rec1 f) where
  algmap f (Rec1 fx) = Rec1 $ algmap @c f fx

instance AlgebraicFunctor c (K1 i a) where
  algmap f (K1 a) = K1 a
  
instance (AlgebraicFunctor c f) => AlgebraicFunctor c (M1 i c' f) where
  algmap f (M1 fx) = M1 $ algmap @c f fx
  
instance (AlgebraicFunctor c f, AlgebraicFunctor c g) => AlgebraicFunctor c (f :+: g) where
  algmap f (L1 fx) = L1 $ algmap @c f fx
  algmap f (R1 gx) = R1 $ algmap @c f gx

instance (AlgebraicFunctor c f, AlgebraicFunctor c g) => AlgebraicFunctor c (f :*: g) where
  algmap f (fx :*: gx) = algmap @c f fx :*: algmap @c f gx

----------------------------------

instance (AlgebraicFunctor (Before f c) g, AlgebraicFunctor c f) => AlgebraicFunctor c (Compose g f) where
  algmap f (Compose gfx) = Compose $ algmap @(Before f c) (algmap @c f) gfx

----------------------------------

data AlgebraicCoyoneda c f x = forall y . (c x, c y) => AlgebraicCoyoneda (y -> x) (f y)

instance (AlgebraicFunctor c f, forall x . d x => c x) => AlgebraicFunctor d (AlgebraicCoyoneda c f) where
  algmap = algmap' @c
    where algmap' :: forall c' x' y' . (c' x', c' y') => (x' -> y') -> AlgebraicCoyoneda c' f x' -> AlgebraicCoyoneda c' f y'
          algmap' f (AlgebraicCoyoneda q fx') = AlgebraicCoyoneda (f . q) fx'
