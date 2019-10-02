module Data.FoldCache where

import Data.Functor
import Control.DeepSeq.Redone

import GHC.Generics

{-| Use this data structure if you want to cache the heavy computation for the methods of @Foldable@.
    In fact, this is the free monad over the list monad, see Control.Monad.Free. -}
data FoldCache x where
  FCQuote :: x -> FoldCache x
  FCConcat :: [FoldCache x] -> FoldCache x
  deriving (Functor, Foldable, Traversable, Generic, Generic1)

instance Applicative FoldCache where
  pure = FCQuote
  FCQuote f <*> fcx = f <$> fcx
  FCConcat fcfs <*> fcx = FCConcat (fcfs <&> (<*> fcx))

instance Monad FoldCache where
  return = FCQuote
  FCQuote x >>= h = h x
  FCConcat fcxs >>= h = FCConcat (fcxs <&> (>>= h))

instance Semigroup (FoldCache x) where
  fcx <> fcy = FCConcat [fcx, fcy]

instance Monoid (FoldCache x) where
  mempty = FCConcat []
  mappend fcx fcy = FCConcat [fcx, fcy]
  mconcat = FCConcat

toFoldCache :: Foldable f => f v -> FoldCache v
toFoldCache = foldMap FCQuote

deriving instance NFData_ FoldCache
