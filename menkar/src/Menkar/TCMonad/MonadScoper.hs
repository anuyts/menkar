module Menkar.TCMonad.MonadScoper where

import Menkar.Syntax.Composable
import Menkar.Syntax.Syntax

class Monad s => MonadScoper s where
  
