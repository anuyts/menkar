module Test.Picker where

import System.Random
import Control.Monad.State
import Data.List.NonEmpty

class Monad m => MonadPicker m where
  pick :: RandomGen g => m a -> State g a

pickLast :: (MonadPicker m, RandomGen g) => g -> m a -> a
pickLast g ma = fst $ runState (pick ma) g 

{-
class Picker a where
  RandomGen g =>
-}
