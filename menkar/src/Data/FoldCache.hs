module Data.FoldCache where

import Data.Functor
import Control.DeepSeq.Redone

import GHC.Generics

{-| Use this data structure if you want to cache the heavy computation for the methods of @Foldable@.
    In fact, this is the free monad over the list monad, see Control.Monad.Free. -}
data FoldCache x where
  FCEmpty :: FoldCache x
  FCPure :: x -> FoldCache x
  FCAppend :: FoldCache x -> FoldCache x -> FoldCache x
  FCMap :: (y -> x) -> FoldCache y -> FoldCache x
  FCBind :: (y -> FoldCache x) -> FoldCache y -> FoldCache x
  --deriving (Functor, Foldable, Traversable, Generic, Generic1)

instance Functor FoldCache where
  fmap = FCMap

instance Foldable FoldCache where
  foldMap h FCEmpty = mempty
  foldMap h (FCPure x) = h x
  foldMap h (FCAppend fcx fcy) = foldMap h fcx <> foldMap h fcy
  foldMap h (FCMap g fcx) = foldMap (h . g) fcx
  foldMap h (FCBind g fcx) = foldMap (foldMap h . g) fcx

instance Applicative FoldCache where
  pure = FCPure
  fcf <*> fcx = fcf >>= \f -> f <$> fcx
  --FCEmpty <*> fcx = FCEmpty
  --FCPure f <*> fcx = f <$> fcx
  --FCAppend fcf fcg <*> fcx = FCAppend (fcf <*> fcx) (fcg <*> fcx)

instance Monad FoldCache where
  return = FCPure
  (>>=) = flip FCBind

instance Semigroup (FoldCache x) where
  (<>) = FCAppend

instance Monoid (FoldCache x) where
  mempty = FCEmpty

toFoldCache :: Foldable f => f v -> FoldCache v
toFoldCache = foldMap FCPure

instance NFData_ FoldCache where
  rnf_ FCEmpty = ()
  rnf_ (FCPure x) = ()
  rnf_ (FCAppend fcx fcy) = rnf_ fcx `seq` rnf_ fcy
  rnf_ (FCMap g fcx) = rnf_ fcx
  rnf_ (FCBind g fcx) = rnf_ fcx
