module Menkar.System.TC where

import Menkar.System.Fine
import Menkar.System.WHN
import Menkar.Fine
import Menkar.Monad.Monad

import Data.Void

class SysWHN sys => SysTC sys where
  checkTermSys :: forall tc v .
    (MonadTC sys tc, DeBruijnLevel v) =>
    Constraint sys ->
    Ctx Type sys v Void ->
    SysTerm sys v ->
    Type sys v ->
    tc ()
  -- see Menkar.TC.Solve.solveMetaAgainstWHNF
  newRelatedSysTerm :: forall tc v vOrig .
    (MonadTC sys tc, Eq v, DeBruijnLevel v, DeBruijnLevel vOrig) =>
    Constraint sys ->
    Degree sys v ->
    Ctx Type sys vOrig Void ->
    Ctx (Twice2 Type) sys v Void ->
    (vOrig -> v) ->
    (v -> Maybe vOrig) ->
    SysTerm sys v ->
    Type sys v ->
    Type sys v ->
    [Int] ->
    [Int] ->
    tc (Term sys vOrig)
