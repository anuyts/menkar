{-# OPTIONS_GHC -fno-cse #-}
{-# LANGUAGE BangPatterns #-}

{-| A Coyoneda type that uses the coyoneda lemma and @unsafePerformIO@ to reduce itself to normal form.

    This module is available under the "cc by-sa 3.0" license:
    https://creativecommons.org/licenses/by-sa/3.0/

    It is based on an answer by the user "dfeuer" on stackoverflow:
    https://stackoverflow.com/a/57494755/2610474
-}

module Data.Functor.Coyoneda.NFUnder where

import qualified Data.Functor.Coyoneda as S
import Data.IORef
import Control.DeepSeq.Picky
import System.IO.Unsafe
import Control.Exception
import Control.Monad

data Coyoneda f a where
  Coyoneda :: (NFData a) => (a -> b) -> f a -> Coyoneda f b

{-| `fmap` happens under the reference, but does NOT traverse `f`. -}
instance Functor (Coyoneda f) where
  fmap f (Coyoneda q fa) = Coyoneda (f . q) fa

instance (Functor f, NFData1 f) => NFData1 (Coyoneda f) where
  rnf1 (Coyoneda q fa) = rwhnf q `seq` rnf1 fa

{-# INLINE liftCoyoneda #-}
liftCoyoneda :: NFData a => f a -> Coyoneda f a
liftCoyoneda = Coyoneda id

{-# INLINE lowerCoyoneda #-}
lowerCoyoneda :: Functor f => Coyoneda f a -> f a
lowerCoyoneda (Coyoneda q fa) = q <$> fa

{-# INLINE hoistCoyoneda #-}
hoistCoyoneda :: (Functor f, Functor g) => (forall x . NFData x => f x -> g x) -> (Coyoneda f a -> Coyoneda g a)
hoistCoyoneda f (Coyoneda g x) = Coyoneda g (f x)

--------------------------

instance (Functor f, Foldable f) => Foldable (Coyoneda f) where
  foldMap f (Coyoneda k a) = foldMap (f . k) a
  {-# INLINE foldMap #-}

{-
instance Traversable f => Traversable (Coyoneda f) where
  traverse f (Coyoneda k a) = liftCoyoneda <$> traverse (f . k) a
  {-# INLINE traverse #-}
-}
