module Menkar.TCMonad.MonadScoper where

import Menkar.Fine.Substitution
import Menkar.Fine.Syntax

class Monad s => MonadScoper
  (mode :: * -> *)
  (modty :: * -> *)
  (rel :: * -> *)
  (s :: * -> *)
  | mode -> modty, mode -> rel where
