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
  deriving (Functor, Foldable, Traversable, Generic, Generic1)

instance Applicative FoldCache where
  pure = FCPure
  FCEmpty <*> fcx = FCEmpty
  FCPure f <*> fcx = f <$> fcx
  FCAppend fcf fcg <*> fcx = FCAppend (fcf <*> fcx) (fcg <*> fcx)

instance Monad FoldCache where
  return = FCPure
  FCEmpty >>= h = FCEmpty
  FCPure x >>= h = h x
  FCAppend fcx fcy >>= h = FCAppend (fcx >>= h) (fcy >>= h)

instance Semigroup (FoldCache x) where
  (<>) = FCAppend

instance Monoid (FoldCache x) where
  mempty = FCEmpty

toFoldCache :: Foldable f => f v -> FoldCache v
toFoldCache = foldMap FCPure

deriving instance NFData_ FoldCache
