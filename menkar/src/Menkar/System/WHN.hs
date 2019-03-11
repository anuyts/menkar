module Menkar.System.WHN where

import Menkar.System.Fine
import Menkar.Fine
import Menkar.Monad.Monad

import Data.Void
import Control.Monad.Writer

class SysSyntax (Term sys) sys => SysWHN sys where
  whnormalizeSys :: MonadTC sys tc =>
    Constraint sys ->
    Ctx Type sys v Void ->
    SysTerm sys v ->
    String ->
    WriterT [Int] tc (Term sys v)
