{-# LANGUAGE UndecidableInstances #-}

module Data.Foldable.Cache where

--import Data.Functor.Functor1
import Control.DeepSeq.Redone

import Data.Functor
import Data.Coerce
import Data.Function

--import GHC.Generics

newtype FoldCache x = FoldCache {getFoldCache :: forall m . Monoid m => (x -> m) -> m}
  deriving (Functor)

instance Foldable FoldCache where
  {-# INLINE foldMap #-}
  foldMap h (FoldCache xs) = xs h

instance Applicative FoldCache where
  {-# INLINE pure #-}
  pure x = FoldCache $ ($ x)
  {-# INLINE (<*>) #-}
  -- There are two implementations, since it's not a commutative monad!
  fs <*> xs = FoldCache $ \h -> foldMap (\f -> foldMap (h . f) xs) fs

instance Monad FoldCache where
  {-# INLINE (>>=) #-}
  xs >>= f = FoldCache $ \h -> foldMap (\x -> foldMap h (f x)) xs

instance Semigroup (FoldCache x) where
  {-# INLINE (<>) #-}
  (!xs) <> (!ys) = FoldCache $ \h -> foldMap h xs <> foldMap h ys

instance Monoid (FoldCache x) where
  {-# INLINE mempty #-}
  mempty = FoldCache $ const mempty

instance NFData_ FoldCache where
  rnf_ = const ()

{-# INLINE toFoldCache #-}
toFoldCache :: Foldable f => f v -> FoldCache v
toFoldCache fv = FoldCache $ \h -> foldMap h fv
