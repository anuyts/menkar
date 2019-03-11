module Menkar.System.TC where

import Menkar.System.Fine
import Menkar.Fine
import Menkar.Monad.Monad

import Data.Void

class SysSyntax (Term sys) sys => SysTC sys where
  checkTermSys :: forall tc v .
    (MonadTC sys tc, DeBruijnLevel v) =>
    Constraint sys ->
    Ctx Type sys v Void ->
    SysTerm sys v ->
    Type sys v ->
    tc ()
