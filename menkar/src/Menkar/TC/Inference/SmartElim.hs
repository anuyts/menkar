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
  ModedModality mode modty v {-^ modality by which the eliminee is used -} ->
  Term mode modty v ->
  Type mode modty v ->
  Term mode modty v ->
  Type mode modty v ->
  tc ()
checkSmartElimDone parent gamma dmuElim eliminee tyEliminee result tyResult = do
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

unbox :: (MonadTC mode modty rel tc) =>
  Constraint mode modty rel ->
  Ctx Type mode modty v Void ->
  ModedModality mode modty v {-^ modality by which the eliminee is used -} ->
  Term mode modty v ->
  Segment Type mode modty v ->
  [SmartEliminator mode modty v] ->
  Term mode modty v ->
  Type mode modty v ->
  tc ()
unbox parent gamma dmuElim eliminee boxSeg eliminators result tyResult = do
  let dmuBox = _segment'modty boxSeg
  let dmuUnbox = ModedModality (modality'dom dmuElim) (approxLeftAdjointProj dmuBox (modality'dom dmuElim))
  dmuElim' <- modedModality4newImplicit gamma
  -- CMODE CMOD : dmuElim = dmuElim' o dmuUnbox
  addNewConstraint
    (JudSmartElim
      gamma
      dmuElim'
      (Expr3 $ TermElim
        (dmuUnbox)
        eliminee
        (Type $ Expr3 $ TermCons $ ConsUniHS $ BoxType boxSeg)
        Unbox
      )
      (_segment'content boxSeg)
      eliminators
      result
      tyResult
    )
    (Just parent)
    "Unboxing."

apply :: (MonadTC mode modty rel tc) =>
  Constraint mode modty rel ->
  Ctx Type mode modty v Void ->
  ModedModality mode modty v {-^ modality by which the eliminee is used -} ->
  Term mode modty v ->
  Binding Type Term mode modty v ->
  Term mode modty v ->
  [SmartEliminator mode modty v] ->
  Term mode modty v ->
  Type mode modty v ->
  tc ()
apply parent gamma dmuElim eliminee piBinding arg eliminators result tyResult = do
  let dmuArg = _segment'modty $ binding'segment $ piBinding
  addNewConstraint
    (JudSmartElim
      gamma
      dmuElim
      (Expr3 $ TermElim
        (idModedModality $ unVarFromCtx <$> ctx'mode gamma)
        eliminee
        (Type $ Expr3 $ TermCons $ ConsUniHS $ Pi piBinding)
        (App arg)
      )
      (Type $ substLast3 arg $ binding'body piBinding)
      eliminators
      result
      tyResult
    )
    (Just parent)
    "Applying function."

insertImplicitArgument :: (MonadTC mode modty rel tc) =>
  Constraint mode modty rel ->
  Ctx Type mode modty v Void ->
  ModedModality mode modty v {-^ modality by which the eliminee is used -} ->
  Term mode modty v ->
  Binding Type Term mode modty v ->
  [SmartEliminator mode modty v] ->
  Term mode modty v ->
  Type mode modty v ->
  tc ()
insertImplicitArgument parent gamma dmuElim eliminee piBinding eliminators result tyResult = do
  let dmuArg = _segment'modty $ binding'segment $ piBinding
  arg <- term4newImplicit (VarFromCtx <$> dmuArg :\\ gamma)
  apply parent gamma dmuElim eliminee piBinding arg eliminators result tyResult

checkSmartElimForNormalType :: (MonadTC mode modty rel tc) =>
  Constraint mode modty rel ->
  Ctx Type mode modty v Void ->
  ModedModality mode modty v {-^ modality by which the eliminee is used -} ->
  Term mode modty v ->
  Type mode modty v ->
  [SmartEliminator mode modty v] ->
  Term mode modty v ->
  Type mode modty v ->
  tc ()
checkSmartElimForNormalType parent gamma dmuElim eliminee tyEliminee eliminators result tyResult =
  case (tyEliminee, eliminators) of
    -- `t ... .e` (bogus)
    -- `t .{...} .e` (bogus)
    (_, SmartElimEnd _ : _ : _) -> tcFail parent $ "Bogus elimination: `...` is not the last eliminator."
    -- `t ...` (end elimination now)
    (_, SmartElimEnd Raw.ArgSpecExplicit : []) ->
      checkSmartElimDone parent gamma dmuElim eliminee tyEliminee result tyResult
    -- `t .{...}` (not syntax)
    (_, SmartElimEnd Raw.ArgSpecNext : []) -> unreachable
    -- `f .{a = ...}` (match argument name)
    (Type (Expr3 (TermCons (ConsUniHS (Pi piBinding)))), SmartElimEnd (Raw.ArgSpecNamed name) : []) ->
      if Just name == (_segment'name $ binding'segment $ piBinding)
      then checkSmartElimDone parent gamma dmuElim eliminee tyEliminee result tyResult
      else case (_segment'plicity $ binding'segment $ piBinding) of
        Explicit -> tcFail parent $ "No argument of this name expected."
        Implicit -> insertImplicitArgument parent gamma dmuElim eliminee piBinding eliminators result tyResult
        Resolves _ -> todo
    -- `boxA .{a = ...}` (unbox)
    (Type (Expr3 (TermCons (ConsUniHS (BoxType boxSeg)))), SmartElimEnd (Raw.ArgSpecNamed name) : []) ->
      unbox parent gamma dmuElim eliminee boxSeg eliminators result tyResult
    -- `t .{a = ...}` (makes no sense)
    (_, SmartElimEnd (Raw.ArgSpecNamed name) : []) -> tcFail parent $ "No argument of this name expected."
    -- `f arg`
    (Type (Expr3 (TermCons (ConsUniHS (Pi piBinding)))), SmartElimArg Raw.ArgSpecExplicit arg : eliminators') ->
      case (_segment'plicity $ binding'segment $ piBinding) of
        Explicit -> apply parent gamma dmuElim eliminee piBinding arg eliminators' result tyResult
        Implicit -> insertImplicitArgument parent gamma dmuElim eliminee piBinding eliminators result tyResult
        Resolves _ -> todo
    -- `f .{arg}`
    (Type (Expr3 (TermCons (ConsUniHS (Pi piBinding)))), SmartElimArg Raw.ArgSpecNext arg : eliminators') ->
      apply parent gamma dmuElim eliminee piBinding arg eliminators' result tyResult
    -- `boxA arg`, `boxA .{arg}`, `boxA .{a = arg}`
    (Type (Expr3 (TermCons (ConsUniHS (BoxType boxSeg)))), SmartElimArg _ _ : eliminators') ->
      unbox parent gamma dmuElim eliminee boxSeg eliminators result tyResult
    (_, _) -> _checkSmartElim

checkSmartElim :: (MonadTC mode modty rel tc) =>
  Constraint mode modty rel ->
  Ctx Type mode modty v Void ->
  ModedModality mode modty v {-^ modality by which the eliminee is used -} ->
  Term mode modty v ->
  Type mode modty v ->
  [SmartEliminator mode modty v] ->
  Term mode modty v ->
  Type mode modty v ->
  tc ()
checkSmartElim parent gamma dmuElim eliminee (Type tyEliminee) eliminators result tyResult = do
  -- whnormalize the type
  (whTyEliminee, metas) <- runWriterT $ whnormalize gamma tyEliminee
  case metas of
    -- the type whnormalizes
    [] -> do
      parent' <- Constraint
                   (JudSmartElim gamma dmuElim eliminee (Type whTyEliminee) eliminators result tyResult)
                   (Just parent)
                   "Weak-head-normalized type."
                   <$> newConstraintID
      checkSmartElimForNormalType parent' gamma dmuElim eliminee (Type whTyEliminee) eliminators result tyResult
    -- the type does not whnormalize
    _ -> blockOnMetas metas parent

