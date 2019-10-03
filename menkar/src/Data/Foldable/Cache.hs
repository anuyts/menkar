{-# LANGUAGE UndecidableInstances #-}

module Data.Foldable.Cache where

import Data.Functor.Functor1
import Control.DeepSeq.Redone

import Data.Functor
import Data.Functor.Compose
import GHC.Generics

{-| Use this data structure if you want to cache the heavy computation for the methods of @Foldable@.
    In fact, this is the free monad over the list monad, see Control.Monad.Free. -}
data FoldCache x where
  FCEmpty :: FoldCache x
  FCPure :: x -> FoldCache x
  FCAppend :: FoldCache x -> FoldCache x -> FoldCache x
  FCMap :: (x -> y) -> FoldCache x -> FoldCache y

instance Functor FoldCache where
  fmap = FCMap

instance Foldable FoldCache where
  foldMap h FCEmpty = mempty
  foldMap h (FCPure x) = h x
  foldMap h (FCAppend fcx fcy) = foldMap h fcx <> foldMap h fcy
  foldMap h (FCMap g fcx) = foldMap (h . g) fcx

instance Applicative FoldCache where
  pure = FCPure
  FCEmpty <*> fcx = FCEmpty
  FCPure f <*> fcx = f <$> fcx
  FCAppend fcf fcg <*> fcx = FCAppend (fcf <*> fcx) (fcg <*> fcx)
  FCMap g fcy <*> fcx = g <$> fcy <*> fcx

instance Monad FoldCache where
  return = FCPure
  FCEmpty >>= h = FCEmpty
  FCPure x >>= h = h x
  FCAppend fcx fcy >>= h = FCAppend (fcx >>= h) (fcy >>= h)
  FCMap g fcx >>= h = fcx >>= h . g

instance Semigroup (FoldCache x) where
  (<>) = FCAppend

instance Monoid (FoldCache x) where
  mempty = FCEmpty

instance NFData_ FoldCache where
  rnf_ FCEmpty = ()
  rnf_ (FCPure x) = ()
  rnf_ (FCAppend fcx fcy) = rnf_ fcx `seq` rnf_ fcy
  rnf_ (FCMap g fcx) = rnf_ fcx

---------------------------------------

class (Foldable f) => FoldableCache f where
  toFoldCache :: f v -> FoldCache v
  default toFoldCache :: (Generic1 f, FoldableCache (Rep1 f)) => f v -> FoldCache v
  toFoldCache = toFoldCache . from1

instance FoldableCache FoldCache where
  {-# INLINE toFoldCache #-}
  toFoldCache = id

---------------------------------------

instance FoldableCache V1 where
  {-# INLINE toFoldCache #-}
  toFoldCache = absurd1

instance FoldableCache U1 where
  {-# INLINE toFoldCache #-}
  toFoldCache = const mempty

instance FoldableCache Par1 where
  {-# INLINE toFoldCache #-}
  toFoldCache = FCPure . unPar1

deriving newtype instance (FoldableCache f) => FoldableCache (Rec1 f)

instance FoldableCache (K1 i c) where
  {-# INLINE toFoldCache #-}
  toFoldCache = const mempty

deriving newtype instance (FoldableCache f) => FoldableCache (M1 i c f)

instance (FoldableCache f, FoldableCache g) => FoldableCache (f :+: g) where
  {-# INLINE toFoldCache #-}
  toFoldCache (L1 fx) = toFoldCache fx
  toFoldCache (R1 gx) = toFoldCache gx

instance (FoldableCache f, FoldableCache g) => FoldableCache (f :*: g) where
  {-# INLINE toFoldCache #-}
  toFoldCache (fx :*: gx) = toFoldCache fx <> toFoldCache gx

instance (FoldableCache f, FoldableCache g) => FoldableCache (f :.: g) where
  {-# INLINE toFoldCache #-}
  toFoldCache (Comp1 fgx) = toFoldCache fgx >>= toFoldCache

instance (FoldableCache f, FoldableCache g) => FoldableCache (Compose f g) where
  {-# INLINE toFoldCache #-}
  toFoldCache (Compose fgx) = toFoldCache fgx >>= toFoldCache

--------------------------------------

instance FoldableCache Maybe where
  toFoldCache = maybe FCEmpty FCPure
deriving instance FoldableCache []
