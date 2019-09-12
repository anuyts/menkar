module Data.Traversable.Maybe where

import Control.Exception.AssertFalse

import Data.Foldable
import Data.Monoid
import Data.Maybe

traverseMaybe :: (Functor t, Foldable t) => (a -> Maybe b) -> t a -> Maybe (t b)
traverseMaybe f ta =
  -- If all contained elements are of the form `Just _`
  if getAll . foldMap (All . isJust . f) $ ta
  -- Then extract the `Just`
  then Just $ fromMaybe unreachable . f <$> ta
  -- Else return `Nothing`
  else Nothing

sequenceMaybe :: (Functor t, Foldable t) => t (Maybe b) -> Maybe (t b)
sequenceMaybe = traverseMaybe id
