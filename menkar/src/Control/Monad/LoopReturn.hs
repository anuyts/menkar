module Control.Monad.LoopReturn where

import Data.Maybe
import Data.Traversable

forReturnList :: (Applicative f) => [a] -> (a -> f (Maybe b)) -> f [b]
forReturnList as f = fmap chopAtNothing $ for as f
  where chopAtNothing :: [Maybe b] -> [b]
        chopAtNothing [] = []
        chopAtNothing (Just b : maybeBs) = b : chopAtNothing maybeBs
        chopAtNothing (Nothing : _) = []
