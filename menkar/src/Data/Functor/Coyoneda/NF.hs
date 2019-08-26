{-# OPTIONS_GHC -fno-cse #-}
{-# LANGUAGE BangPatterns #-}

{-| A Coyoneda type that uses the coyoneda lemma and @unsafePerformIO@ to reduce itself to normal form.

    This module is available under the "cc by-sa 3.0" license:
    https://creativecommons.org/licenses/by-sa/3.0/

    It is based on an answer by the user "dfeuer" on stackoverflow:
    https://stackoverflow.com/a/57494755/2610474
-}

module Data.Functor.Coyoneda.NF (
  module Data.Functor.Coyoneda
  ) where

import Data.Functor.Coyoneda

{-
import qualified Data.Functor.Coyoneda as S
import Data.IORef
import Control.DeepSeq.Redone
import System.IO.Unsafe
import Control.Exception
import Control.Monad

newtype Coyoneda f a = UnsafeCoyonedaFromRef {unsafeCoyonedaToRef :: IORef (S.Coyoneda f a, Bool)}

-- | The boolean tells whether in normal form.
newCoyonedaIO :: (S.Coyoneda f a, Bool) -> IO (Coyoneda f a)
newCoyonedaIO c = UnsafeCoyonedaFromRef <$> newIORef c

{-# NOINLINE newCoyoneda #-}
newCoyoneda :: S.Coyoneda f a -> Coyoneda f a
newCoyoneda = unsafePerformIO . newCoyonedaIO . (, False)

unsafeReadCoyonedaIO :: Coyoneda f a -> IO (S.Coyoneda f a, Bool)
unsafeReadCoyonedaIO (UnsafeCoyonedaFromRef ref) = readIORef ref

{-# NOINLINE unsafeReadCoyoneda #-}
unsafeReadCoyoneda :: Coyoneda f a -> (S.Coyoneda f a, Bool) 
unsafeReadCoyoneda = unsafePerformIO . unsafeReadCoyonedaIO

{-| This is relatively safe for lawful functors. -}
readCoyoneda :: Functor f => Coyoneda f a -> S.Coyoneda f a
readCoyoneda = fst . unsafeReadCoyoneda

{-| `fmap` happens under the reference, but does NOT traverse `f`. -}
instance Functor (Coyoneda f) where
  {-# NOINLINE fmap #-}
  fmap f c = unsafePerformIO $ do
    (q, isInNF) <- unsafeReadCoyonedaIO c
    newCoyonedaIO $ (fmap f q, False)

instance (Functor f, NFData1 f) => NFData1 (Coyoneda f) where
  {-# NOINLINE liftRnf #-}
  liftRnf f (UnsafeCoyonedaFromRef ref) = unsafePerformIO $ do
    (co, isInNF) <- readIORef ref
    unless isInNF $ do
      let fx = S.lowerCoyoneda co
      -- We use evaluate because we want to be really sure the reduction to NF
      -- succeeds and we don't install bottom in the IORef.
      evaluate (liftRnf f fx)
      writeIORef ref (S.liftCoyoneda fx, True)

{-# INLINE liftCoyoneda #-}
liftCoyoneda :: f a -> Coyoneda f a
liftCoyoneda = newCoyoneda . S.liftCoyoneda

{-# INLINE lowerCoyoneda #-}
lowerCoyoneda :: Functor f => Coyoneda f a -> f a
lowerCoyoneda = S.lowerCoyoneda . readCoyoneda

{-| This is relatively safe for lawful functors. -}
pattern Coyoneda ::
  forall f y . (Functor f) =>
  forall x . () => (x -> y) -> f x ->
  Coyoneda f y
pattern Coyoneda q fx <- (readCoyoneda -> S.Coyoneda q fx)
  where Coyoneda q fx = newCoyoneda $ S.Coyoneda q fx
{-# COMPLETE Coyoneda #-}

{-# INLINE hoistCoyoneda #-}
hoistCoyoneda :: (Functor f, Functor g) => (forall x . f x -> g x) -> (Coyoneda f a -> Coyoneda g a)
hoistCoyoneda f (Coyoneda g x) = Coyoneda g (f x)

--------------------------

instance (Functor f, Foldable f) => Foldable (Coyoneda f) where
  foldMap f (Coyoneda k a) = foldMap (f . k) a
  {-# INLINE foldMap #-}

instance Traversable f => Traversable (Coyoneda f) where
  traverse f (Coyoneda k a) = liftCoyoneda <$> traverse (f . k) a
  {-# INLINE traverse #-}
-}
