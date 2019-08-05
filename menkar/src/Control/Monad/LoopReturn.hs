module Control.Monad.LoopReturn where

import Data.Maybe
import Data.Traversable

-- | Runs all computations in the list from left to right, until one returns @Right _@.
forReturnList :: (Monad f) => [a] -> (a -> f (Either b c)) -> f ([b], Maybe c)
forReturnList [] f = return ([], Nothing)
forReturnList (a : as) f = do
  fa <- f a
  case fa of
    Left b -> do
      (bs, maybeC) <- forReturnList as f
      return (b : bs, maybeC)
    Right c -> return ([], Just c)
