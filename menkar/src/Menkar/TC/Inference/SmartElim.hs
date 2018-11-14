module Menkar.TC.Inference.SmartElim where

import Menkar.Fine.Syntax
import Menkar.Basic.Context
import Menkar.Fine.Context
import Menkar.Fine.Judgement
import Menkar.Fine.Multimode
import Menkar.Fine.LookupQName
import qualified Menkar.Raw.Syntax as Raw
import Menkar.TC.Monad
import Control.Exception.AssertFalse
import Menkar.Fine.WHNormalize

import Data.Void
import Control.Lens
import Data.Functor.Compose
import Control.Monad
import Control.Monad.Writer.Lazy

-- CMODE means you need to check a mode
-- CMODTY means you need to check a modality

-------

checkSmartElimDone :: (MonadTC mode modty rel tc) =>
  Constraint mode modty rel ->
  Ctx Type mode modty v Void ->
  Term mode modty v ->
  Type mode modty v ->
  Term mode modty v ->
  Type mode modty v ->
  tc ()
checkSmartElimDone parent gamma eliminee tyEliminee result tyResult = do
      addNewConstraint
        (JudTypeRel
          eqDeg
          (duplicateCtx gamma)
          (Pair3 tyEliminee tyResult)
        )
        (Just parent)
        "End of elimination: checking if types match."
      addNewConstraint
        (JudTermRel
          eqDeg
          (duplicateCtx gamma)
          (Pair3 eliminee result)
          (Pair3 tyEliminee tyResult)
        )
        (Just parent)
        "End of elimination: checking if types match"

checkSmartElimForNormalType :: (MonadTC mode modty rel tc) =>
  Constraint mode modty rel ->
  Ctx Type mode modty v Void ->
  Term mode modty v ->
  Type mode modty v ->
  [SmartEliminator mode modty v] ->
  Term mode modty v ->
  Type mode modty v ->
  tc ()
checkSmartElimForNormalType parent gamma eliminee tyEliminee eliminators result tyResult =
  case (tyEliminee, eliminators) of
    -- `t ... .e` (bogus)
    -- `t .{...} .e` (bogus)
    (_, SmartElimEnd _ : _ : _) -> tcFail parent $ "Bogus elimination: `...` is not the last eliminator."
    -- `t ...` (end elimination now)
    (_, SmartElimEnd Raw.ArgSpecExplicit : []) ->
      checkSmartElimDone parent gamma eliminee tyEliminee result tyResult
    -- `t .{...}` (not syntax)
    (_, SmartElimEnd Raw.ArgSpecNext : []) -> unreachable
    -- `f .{a = ...}` (match argument name)
    (Type (Expr3 (TermCons (ConsUniHS (Pi piBinding)))), SmartElimEnd (Raw.ArgSpecNamed name) : []) ->
      if Just name == (_segment'name $ binding'segment $ piBinding)
      then checkSmartElimDone parent gamma eliminee tyEliminee result tyResult
      else case (_segment'plicity $ binding'segment $ piBinding) of
        Explicit -> tcFail parent $ "No argument of this name expected."
        Implicit -> _
        Resolves _ -> todo
    (_, _) -> _checkSmartElim

checkSmartElim :: (MonadTC mode modty rel tc) =>
  Constraint mode modty rel ->
  Ctx Type mode modty v Void ->
  Term mode modty v ->
  Type mode modty v ->
  [SmartEliminator mode modty v] ->
  Term mode modty v ->
  Type mode modty v ->
  tc ()
checkSmartElim parent gamma eliminee (Type tyEliminee) eliminators result tyResult = do
  (whTyEliminee, metas) <- runWriterT $ whnormalize gamma tyEliminee
  case metas of
    [] -> do
      parent' <- Constraint
                   (JudSmartElim gamma eliminee (Type whTyEliminee) eliminators result tyResult)
                   (Just parent)
                   "Weak-head-normalized type."
                   <$> newConstraintID
      checkSmartElimForNormalType parent' gamma eliminee (Type whTyEliminee) eliminators result tyResult
    _ -> blockOnMetas metas parent

