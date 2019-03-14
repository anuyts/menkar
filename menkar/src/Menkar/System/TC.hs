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
  -- see Menkar.TC.Rel
  checkTermRelSysTermWHNTerm :: forall tc v .
    (MonadTC sys tc, DeBruijnLevel v) =>
    Constraint sys ->
    Degree sys v ->
    Ctx (Twice2 Type) sys v Void ->
    SysTerm sys v ->
    Term sys v ->
    Type sys v ->
    Type sys v ->
    [Int] ->
    [Int] ->
    tc ()
  -- | see Menkar.TC.Judgement.checkEta.
  -- | This will generally be unreachable, unless a system introduces types via SysTerm.
  checkEtaWHNSysTy :: forall tc v .
    (MonadTC sys tc, DeBruijnLevel v) =>
    Constraint sys ->
    Ctx Type sys v Void ->
    Term sys v ->
    SysTerm sys v {-^ The type -} ->
    tc ()
  -- | Check @'JudMode'@.
  checkMode :: forall tc v .
    (MonadTC sys tc, DeBruijnLevel v) =>
    Constraint sys ->
    Ctx Type sys v Void ->
    Mode sys v ->
    tc ()
  -- | Check @'JudModeRel'@.
  checkModeRel :: forall tc v .
    (MonadTC sys tc, DeBruijnLevel v) =>
    Constraint sys ->
    Ctx (Twice2 Type) sys v Void ->
    Mode sys v ->
    Mode sys v ->
    tc ()
  checkModality :: forall tc v .
    (MonadTC sys tc, DeBruijnLevel v) =>
    Constraint sys ->
    Ctx Type sys v Void ->
    Modality sys v ->
    Mode sys v ->
    Mode sys v ->
    tc ()
  checkModalityRel :: forall tc v .
    (MonadTC sys tc, DeBruijnLevel v) =>
    Constraint sys ->
    ModRel ->
    Ctx (Twice2 Type) sys v Void ->
    Modality sys v ->
    Modality sys v ->
    Mode sys v ->
    Mode sys v ->
    tc ()
  checkSysJudgement :: forall tc .
    (MonadTC sys tc) =>
    Constraint sys ->
    SysJudgement sys ->
    tc ()
