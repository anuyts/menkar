{-# OPTIONS_GHC -fno-cse #-}
{-# LANGUAGE BangPatterns #-}

{-| A Coyoneda type that uses the coyoneda lemma and @unsafePerformIO@ to reduce itself to normal form.

    This module is available under the "cc by-sa 3.0" license:
    https://creativecommons.org/licenses/by-sa/3.0/

    It is based on an answer by the user "dfeuer" on stackoverflow:
-}

module Data.Functor.Coyoneda.NF where

import qualified Data.Functor.Coyoneda as S
import Data.IORef
import Control.DeepSeq
import System.IO.Unsafe
import Control.Exception

newtype Coyoneda f a = UnsafeCoyonedaFromRef {unsafeCoyonedaToRef :: IORef (S.Coyoneda f a)}

newCoyonedaIO :: S.Coyoneda f a -> IO (Coyoneda f a)
newCoyonedaIO c = UnsafeCoyonedaFromRef <$> newIORef c

{-# NOINLINE newCoyoneda #-}
newCoyoneda :: S.Coyoneda f a -> Coyoneda f a
newCoyoneda = unsafePerformIO . newCoyonedaIO

unsafeReadCoyonedaIO :: Coyoneda f a -> IO (S.Coyoneda f a)
unsafeReadCoyonedaIO (UnsafeCoyonedaFromRef ref) = readIORef ref

{-# NOINLINE unsafeReadCoyoneda #-}
unsafeReadCoyoneda :: Coyoneda f a -> S.Coyoneda f a
unsafeReadCoyoneda = unsafePerformIO . unsafeReadCoyonedaIO

{-| This is relatively safe for lawful functors. -}
readCoyoneda :: Functor f => Coyoneda f a -> S.Coyoneda f a
readCoyoneda = unsafeReadCoyoneda

{-| `fmap` happens under the reference, but does NOT traverse `f`. -}
instance Functor (Coyoneda f) where
  {-# NOINLINE fmap #-}
  fmap f c = unsafePerformIO $ do
    q <- unsafeReadCoyonedaIO c
    newCoyonedaIO $ fmap f q

instance (Functor f, NFData (f a)) => NFData (Coyoneda f a) where
  {-# NOINLINE rnf #-}
  rnf (UnsafeCoyonedaFromRef ref) = unsafePerformIO $ do
    co <- readIORef ref
    let !fx = S.lowerCoyoneda co
    -- We use evaluate because we want to be really sure the reduction to NF
    -- succeeds and we don't install bottom in the IORef.
    evaluate (rnf fx)
    writeIORef ref (S.liftCoyoneda fx)

liftCoyoneda :: f a -> Coyoneda f a
liftCoyoneda = newCoyoneda . S.liftCoyoneda

lowerCoyoneda :: Functor f => Coyoneda f a -> f a
lowerCoyoneda = S.lowerCoyoneda . unsafeReadCoyoneda

{-| This is relatively safe for lawful functors. -}
pattern Coyoneda ::
  forall f y . (Functor f) =>
  forall x . () => (x -> y) -> f x ->
  Coyoneda f y
pattern Coyoneda q fx <- (readCoyoneda -> S.Coyoneda q fx)
  where Coyoneda q fx = newCoyoneda $ S.Coyoneda q fx
{-# COMPLETE Coyoneda #-}

hoistCoyoneda :: (Functor f, Functor g) => (forall a. f a -> g a) -> (Coyoneda f b -> Coyoneda g b)
hoistCoyoneda f (Coyoneda g x) = Coyoneda g (f x)
