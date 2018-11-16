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

projFst :: (MonadTC mode modty rel tc) =>
  Constraint mode modty rel ->
  Ctx Type mode modty v Void ->
  ModedModality mode modty v {-^ modality by which the eliminee is used -} ->
  Term mode modty v ->
  Binding Type Term mode modty v ->
  [SmartEliminator mode modty v] ->
  Term mode modty v ->
  Type mode modty v ->
  tc ()
projFst parent gamma dmuElim eliminee sigmaBinding eliminators result tyResult = do
  let dmuSigma = _segment'modty $ binding'segment sigmaBinding
  let dmuProjFst = ModedModality (modality'dom dmuElim) (approxLeftAdjointProj dmuSigma (modality'dom dmuElim))
  dmuElim' <- modedModality4newImplicit gamma
  -- CMODE CMOD : dmuElim = dmuElim' o dmuProjFst
  addNewConstraint
    (JudSmartElim
      gamma
      dmuElim'
      (Expr3 $ TermElim
        (dmuProjFst)
        eliminee
        (Type $ Expr3 $ TermCons $ ConsUniHS $ Sigma sigmaBinding)
        Fst
      )
      (_segment'content $ binding'segment sigmaBinding)
      eliminators
      result
      tyResult
    )
    (Just parent)
    "First projection."

projSnd :: (MonadTC mode modty rel tc) =>
  Constraint mode modty rel ->
  Ctx Type mode modty v Void ->
  ModedModality mode modty v {-^ modality by which the eliminee is used -} ->
  Term mode modty v ->
  Binding Type Term mode modty v ->
  [SmartEliminator mode modty v] ->
  Term mode modty v ->
  Type mode modty v ->
  tc ()
projSnd parent gamma dmuElim eliminee sigmaBinding eliminators result tyResult = do
  let dmuSigma = _segment'modty $ binding'segment sigmaBinding
  let dmuProjFst = ModedModality (modality'dom dmuElim) (approxLeftAdjointProj dmuSigma (modality'dom dmuElim))
  let tmFst = (Expr3 $ TermElim
                (dmuProjFst)
                eliminee
                (Type $ Expr3 $ TermCons $ ConsUniHS $ Sigma sigmaBinding)
                Fst
              )
  let tmSnd = (Expr3 $ TermElim
                (idModedModality $ unVarFromCtx <$> ctx'mode gamma)
                eliminee
                (Type $ Expr3 $ TermCons $ ConsUniHS $ Sigma sigmaBinding)
                Snd
              )
  addNewConstraint
    (JudSmartElim
      gamma
      dmuElim
      tmSnd
      (Type $ substLast3 tmFst $ binding'body sigmaBinding)
      eliminators
      result
      tyResult
    )
    (Just parent)
    "Second projection."

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

autoEliminate :: (MonadTC mode modty rel tc) =>
  Constraint mode modty rel ->
  Ctx Type mode modty v Void ->
  ModedModality mode modty v {-^ modality by which the eliminee is used -} ->
  Term mode modty v ->
  Type mode modty v ->
  [SmartEliminator mode modty v] ->
  Term mode modty v ->
  Type mode modty v ->
  tc ()
autoEliminate parent gamma dmuElim eliminee tyEliminee eliminators result tyResult = do
  case tyEliminee of
    Type (Expr3 (TermCons (ConsUniHS (Pi piBinding)))) ->
      case (_segment'plicity $ binding'segment $ piBinding) of
        Explicit -> tcFail parent $ "Cannot auto-eliminate."
        Implicit -> insertImplicitArgument parent gamma dmuElim eliminee piBinding eliminators result tyResult
        Resolves _ -> todo
    Type (Expr3 (TermCons (ConsUniHS (BoxType boxSeg)))) ->
      unbox parent gamma dmuElim eliminee boxSeg eliminators result tyResult
    _ -> tcFail parent $ "Cannot auto-eliminate."

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
    -- `t ... e`, `t .{...} e` (bogus)
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
      else autoEliminate parent gamma dmuElim eliminee tyEliminee eliminators result tyResult
    -- `t .{a = ...}`
    (_, SmartElimEnd (Raw.ArgSpecNamed name) : []) ->
      autoEliminate parent gamma dmuElim eliminee tyEliminee eliminators result tyResult
    -- `f arg`
    (Type (Expr3 (TermCons (ConsUniHS (Pi piBinding)))), SmartElimArg Raw.ArgSpecExplicit arg : eliminators') ->
      case (_segment'plicity $ binding'segment $ piBinding) of
        Explicit -> apply parent gamma dmuElim eliminee piBinding arg eliminators' result tyResult
        _ -> autoEliminate parent gamma dmuElim eliminee tyEliminee eliminators result tyResult
    -- `f .{arg}`
    (Type (Expr3 (TermCons (ConsUniHS (Pi piBinding)))), SmartElimArg Raw.ArgSpecNext arg : eliminators') ->
      apply parent gamma dmuElim eliminee piBinding arg eliminators' result tyResult
    -- `f .{a = arg}`
    (Type (Expr3 (TermCons (ConsUniHS (Pi piBinding)))), SmartElimArg (Raw.ArgSpecNamed name) arg : eliminators') ->
      if Just name == (_segment'name $ binding'segment $ piBinding)
      then apply parent gamma dmuElim eliminee piBinding arg eliminators' result tyResult
      else autoEliminate parent gamma dmuElim eliminee tyEliminee eliminators result tyResult
    -- `t arg`, `t .{arg}`, `t .{a = arg}`
    (_, SmartElimArg _ _ : eliminators') ->
      autoEliminate parent gamma dmuElim eliminee tyEliminee eliminators result tyResult
    -- `pair .componentName`
    (Type (Expr3 (TermCons (ConsUniHS (Sigma sigmaBinding)))), SmartElimProj (Raw.ProjSpecNamed name) : eliminators') ->
      -- if the given name is the name of the first component
      if Just name == (_segment'name $ binding'segment $ sigmaBinding)
      -- then project out the first component and continue
      then projFst parent gamma dmuElim eliminee sigmaBinding eliminators' result tyResult
      -- else project out the second component and try again
      else projSnd parent gamma dmuElim eliminee sigmaBinding eliminators result tyResult
    -- `pair .i`
    (Type (Expr3 (TermCons (ConsUniHS (Sigma sigmaBinding)))), SmartElimProj (Raw.ProjSpecNumbered i) : eliminators') ->
      if i == 1
      -- then project out the first component and continue
      then projFst parent gamma dmuElim eliminee sigmaBinding eliminators' result tyResult
      -- else project out the second component and decrement
      else let decEliminators = SmartElimProj (Raw.ProjSpecNumbered $ i - 1) : eliminators'
           in  projSnd parent gamma dmuElim eliminee sigmaBinding decEliminators result tyResult
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
