{-# LANGUAGE FlexibleContexts, FlexibleInstances, ApplicativeDo, MultiParamTypeClasses #-}

module Menkar.Scoper where

import Menkar.TCMonad.MonadScoper
import qualified Menkar.Raw as Raw

--scEntry :: MonadScoper s => Raw.Entry -> 



{-
{-| @'Spawns' 'u' 'f'@ means that new unique values of type 'u' can be obtained inside 'f'.
    prop> ('==') '<$>' 'spawn' '<*>' 'spawn' = 'False' '<$' 'spawn' '<*' 'spawn'
-}
class (Eq u, Applicative f) => Spawns u f where
  spawn :: f u

class (Monad m, Spawns u m) => CanPostparse u m where

---------------------------

-}
