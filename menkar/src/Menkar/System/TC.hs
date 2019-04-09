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
    ModedDegree sys v ->
    Ctx Type sys vOrig Void ->
    Ctx (Twice2 Type) sys v Void ->
    (vOrig -> v) ->
    (v -> Maybe vOrig) ->
    SysTerm sys v ->
    Type sys v ->
    Type sys v ->
    (String -> tc ()) ->
    tc (Maybe (Term sys vOrig))
  -- see Menkar.TC.Rel
  checkTermRelSysTermWHNTermNoEta :: forall tc v .
    (MonadTC sys tc, DeBruijnLevel v) =>
    Constraint sys ->
    ModedDegree sys v ->
    Ctx (Twice2 Type) sys v Void ->
    SysTerm sys v ->
    Term sys v ->
    Type sys v ->
    Type sys v ->
    [Int] ->
    [Int] ->
    tc ()
  -- | see Menkar.TC.Solve.checkEta.
  -- | This will generally yield false, unless a system introduces types with eta via SysTerm.
  -- | ABOLISH THIS: eta isn't supported for non-universe types.
  checkEtaWHNSysTy :: forall tc v .
    (MonadTC sys tc, DeBruijnLevel v) =>
    Constraint sys ->
    Ctx Type sys v Void ->
    Term sys v ->
    SysTerm sys v {-^ The type -} ->
    tc Bool

  checkSysUniHSConstructor :: forall tc v .
    (MonadTC sys tc, DeBruijnLevel v) =>
    Constraint sys ->
    Ctx Type sys v Void ->
    SysUniHSConstructor sys v ->
    Type sys v ->
    tc ()
  -- | See Menkar.TC.Solve
  newRelatedSysUniHSConstructor :: forall tc v vOrig .
    (MonadTC sys tc, Eq v, DeBruijnLevel v, DeBruijnLevel vOrig) =>
    Constraint sys ->
    ModedDegree sys v ->
    Ctx Type sys vOrig Void ->
    Ctx (Twice2 Type) sys v Void ->
    (vOrig -> v) ->
    (v -> Maybe vOrig) ->
    SysUniHSConstructor sys v ->
    tc (SysUniHSConstructor sys vOrig)
  etaExpandSysType :: forall tc v .
    (MonadTC sys tc, DeBruijnLevel v) =>
    Constraint sys ->
    Ctx Type sys v Void ->
    Term sys v ->
    SysUniHSConstructor sys v ->
    tc (Maybe (Maybe (Term sys v)))
  checkSysUniHSConstructorRel :: forall tc v .
    (MonadTC sys tc, DeBruijnLevel v) =>
    Constraint sys ->
    ModedDegree sys v ->
    Ctx (Twice2 Type) sys v Void ->
    SysUniHSConstructor sys v ->
    SysUniHSConstructor sys v ->
    Type sys v ->
    Type sys v ->
    [Int] ->
    [Int] ->
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
