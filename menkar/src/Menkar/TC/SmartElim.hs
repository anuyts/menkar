module Menkar.TC.SmartElim where

import Menkar.System.Fine
import Menkar.System.TC
import Menkar.Fine.Syntax
import Menkar.Basic.Context
import Menkar.Fine.Context
import Menkar.Fine.Judgement
import Menkar.Fine.LookupQName
import qualified Menkar.Raw.Syntax as Raw
import Menkar.Monad.Monad
import Control.Exception.AssertFalse
import Menkar.WHN

import Data.Void
import Control.Lens
import Data.Functor.Compose
import Control.Monad
import Control.Monad.Writer.Lazy
import Control.Monad.Trans.Maybe

-- CMODE means you need to check a mode
-- CMODTY means you need to check a modality

-------

{-| Handles a smartelim-judgement with 0 eliminations.
-}
checkSmartElimDone :: forall sys tc v .
  (SysTC sys, MonadTC sys tc, DeBruijnLevel v) =>
  Constraint sys ->
  Ctx Type sys v Void {-^ The context of the SmartElim judgement, or equivalently of its result. -} ->
  Term sys v ->
  Type sys v ->
  Term sys v ->
  Type sys v ->
  tc ()
checkSmartElimDone parent gamma eliminee tyEliminee result tyResult = do
      addNewConstraint
        (JudTypeRel
          (eqDeg :: Degree sys _)
          (duplicateCtx gamma)
          (Twice2 tyEliminee tyResult)
        )
        (Just parent)
        "End of elimination: checking if types match."
      addNewConstraint
        (JudTermRel
          (eqDeg :: Degree sys _)
          (duplicateCtx gamma)
          (Twice2 eliminee result)
          (Twice2 tyEliminee tyResult)
        )
        (Just parent)
        "End of elimination: checking if results match"

unbox :: forall sys tc v .
  (SysTC sys, MonadTC sys tc, DeBruijnLevel v) =>
  Constraint sys ->
  Ctx Type sys v Void {-^ The context of the SmartElim judgement, or equivalently of its result. -} ->
  Term sys v ->
  Segment Type sys v ->
  ModedModality sys v {-^ The modality by which we need to unbox (likely to be inferred.) -} ->
  [Pair2 ModedModality SmartEliminator sys v] {-^ The remaining eliminators (not including unbox). -} ->
  Term sys v ->
  Type sys v ->
  tc ()
unbox parent gamma eliminee boxSeg dmuInfer eliminators result tyResult = do
  let dgamma :: Mode sys v = unVarFromCtx <$> ctx'mode gamma
  let dmuBox :: ModedModality sys v = _segment'modty boxSeg
  let dmuUnbox :: ModedModality sys v = modedApproxLeftAdjointProj dmuBox (modality'dom dmuInfer)
  let dmuElim' = concatModedModalityDiagrammatically (fst2 <$> eliminators) dgamma
  -- CMODE CMOD : = dmuElim' o dmuUnbox
  -- CMODE : check if you can unbox
  addNewConstraint
    (JudModalityRel ModEq
      (crispModedModality :\\ duplicateCtx gamma)
      (modality'mod dmuUnbox)
      (modality'mod dmuInfer)
      (modality'dom dmuInfer)
      (modality'dom dmuElim')
    )
    (Just parent)
    "Checking whether actual modality equals expected modality."
  addNewConstraint
    (JudSmartElim
      gamma
      (Expr2 $ TermElim
        (dmuUnbox)
        eliminee
        (BoxType boxSeg)
        Unbox
      )
      (_segment'content boxSeg)
      eliminators
      result
      tyResult
    )
    (Just parent)
    "Unboxing."

projFst ::
  (SysTC sys, MonadTC sys tc, DeBruijnLevel v) =>
  Constraint sys ->
  Ctx Type sys v Void {-^ The context of the SmartElim judgement, or equivalently of its result. -} ->
  Term sys v ->
  Binding Type Term sys v ->
  [Pair2 ModedModality SmartEliminator sys v] ->
  Term sys v ->
  Type sys v ->
  tc ()
projFst parent gamma eliminee sigmaBinding eliminators result tyResult = do
  let dmuSigma = _segment'modty $ binding'segment sigmaBinding
  let dmuProjFst = ModedModality (modality'dom dmuElim) (approxLeftAdjointProj dmuSigma (modality'dom dmuElim))
  dmuElim' <- newMetaModedModality (Just parent) gamma "Mode/modality for remainder of elimination."
  -- CMODE CMOD : = dmuElim' o dmuProjFst
  addNewConstraint
    (JudSmartElim
      gamma
      dmuElim'
      (Expr2 $ TermElim
        (dmuProjFst)
        eliminee
        (Sigma sigmaBinding)
        Fst
      )
      (_segment'content $ binding'segment sigmaBinding)
      eliminators
      result
      tyResult
    )
    (Just parent)
    "First projection."

projSnd ::
  (SysTC sys, MonadTC sys tc, DeBruijnLevel v) =>
  Constraint sys ->
  Ctx Type sys v Void {-^ The context of the SmartElim judgement, or equivalently of its result. -} ->
  Term sys v ->
  Binding Type Term sys v ->
  [Pair2 ModedModality SmartEliminator sys v] ->
  Term sys v ->
  Type sys v ->
  tc ()
projSnd parent gamma eliminee sigmaBinding eliminators result tyResult = do
  let dmuSigma = _segment'modty $ binding'segment sigmaBinding
  let dmuProjFst = ModedModality (modality'dom dmuElim) (approxLeftAdjointProj dmuSigma (modality'dom dmuElim))
  let tmFst = (Expr2 $ TermElim
                (dmuProjFst)
                eliminee
                (Sigma sigmaBinding)
                Fst
              )
  let tmSnd = (Expr2 $ TermElim
                (idModedModality $ unVarFromCtx <$> ctx'mode gamma)
                eliminee
                (Sigma sigmaBinding)
                Snd
              )
  addNewConstraint
    (JudSmartElim
      gamma
      dmuElim
      tmSnd
      (Type $ substLast2 tmFst $ binding'body sigmaBinding)
      eliminators
      result
      tyResult
    )
    (Just parent)
    "Second projection."

apply ::
  (SysTC sys, MonadTC sys tc, DeBruijnLevel v) =>
  Constraint sys ->
  Ctx Type sys v Void {-^ The context of the SmartElim judgement, or equivalently of its result. -} ->
  Term sys v ->
  Binding Type Term sys v ->
  Term sys v ->
  [Pair2 ModedModality SmartEliminator sys v] ->
  Term sys v ->
  Type sys v ->
  tc ()
apply parent gamma eliminee piBinding arg eliminators result tyResult = do
  let dmuArg = _segment'modty $ binding'segment $ piBinding
  addNewConstraint
    (JudTerm
      (wildModedModality :\\ gamma) -- CMODE
      arg
      (_decl'content $ binding'segment $ piBinding)
    )
    (Just parent)
    "Applying function: checking argument."
  addNewConstraint
    (JudSmartElim
      gamma
      dmuElim
      (Expr2 $ TermElim
        (idModedModality $ unVarFromCtx <$> ctx'mode gamma)
        eliminee
        (Pi piBinding)
        (App arg)
      )
      (Type $ substLast2 arg $ binding'body piBinding)
      eliminators
      result
      tyResult
    )
    (Just parent)
    "Applying function: checking further elimination."

insertImplicitArgument :: forall sys tc v .
  (SysTC sys, MonadTC sys tc, DeBruijnLevel v) =>
  Constraint sys ->
  Ctx Type sys v Void {-^ The context of the SmartElim judgement, or equivalently of its result. -} ->
  Term sys v ->
  Binding Type Term sys v ->
  [Pair2 ModedModality SmartEliminator sys v] ->
  Term sys v ->
  Type sys v ->
  tc ()
insertImplicitArgument parent gamma eliminee piBinding eliminators result tyResult = do
  let dmuArg = _segment'modty $ binding'segment $ piBinding
  let tyArg = _segment'content $ binding'segment $ piBinding
  -- CMOD: degree should be multiplied by dmuArg here!
  arg <- newMetaTerm (Just parent) (eqDeg :: Degree sys _) (VarFromCtx <$> dmuArg :\\ gamma)
           tyArg True "Inferring implicit argument."
  apply parent gamma eliminee piBinding arg eliminators result tyResult

{-| Tries to apply an implicit elimination to the eliminee.
    If successful, creates a new constraint with the once eliminated eliminee and the same eliminators.
    If unsuccesful, calls the alternative if present, or throws a @'tcFail'@.
-}
autoEliminate ::
  (SysTC sys, MonadTC sys tc, DeBruijnLevel v) =>
  Constraint sys ->
  Ctx Type sys v Void {-^ The context of the SmartElim judgement, or equivalently of its result. -} ->
  Term sys v ->
  Type sys v ->
  [Pair2 ModedModality SmartEliminator sys v] ->
  Term sys v ->
  Type sys v ->
  Maybe (tc ()) ->
  tc ()
autoEliminate parent gamma eliminee tyEliminee eliminators result tyResult maybeAlternative = do
  let alternative = case maybeAlternative of
           Nothing -> tcFail parent $ "Cannot auto-eliminate."
           Just alternative' -> alternative'
  case tyEliminee of
    Type (Expr2 (TermCons (ConsUniHS (Pi piBinding)))) ->
      case (_segment'plicity $ binding'segment $ piBinding) of
        Explicit -> alternative
        Implicit -> insertImplicitArgument parent gamma eliminee piBinding eliminators result tyResult
        Resolves _ -> todo
    Type (Expr2 (TermCons (ConsUniHS (BoxType boxSeg)))) ->
      unbox parent gamma eliminee boxSeg eliminators result tyResult
    _ -> alternative

checkSmartElimForNormalType ::
  (SysTC sys, MonadTC sys tc, DeBruijnLevel v) =>
  Constraint sys ->
  Ctx Type sys v Void {-^ The context of the SmartElim judgement, or equivalently of its result. -} ->
  Term sys v ->
  Type sys v ->
  [Pair2 ModedModality SmartEliminator sys v] ->
  Term sys v ->
  Type sys v ->
  tc ()
checkSmartElimForNormalType parent gamma eliminee tyEliminee eliminators result tyResult =
  case (tyEliminee, eliminators) of
    -- No eliminators: Check that it's done. (Previously claimed to be unreachable, but I don't see why.)
    (_, []) ->
      --unreachable
      checkSmartElimDone parent gamma eliminee tyEliminee result tyResult
    -- Silently eliminate further: `t ...` (Auto-eliminate, if not possible, assert that it's done.)
    (_, SmartElimDots : []) ->
      autoEliminate parent gamma eliminee tyEliminee eliminators result tyResult $
      Just $ checkSmartElimDone parent gamma eliminee tyEliminee result tyResult
    -- Bogus: `t ... e` (Throw error.)
    (_, SmartElimDots : _) -> tcFail parent $ "Bogus elimination: `...` is not the last eliminator."
    -- Explicit application of a function: `f arg` (Apply if explicit, auto-eliminate otherwise.)
    (Type (Expr2 (TermCons (ConsUniHS (Pi piBinding)))), SmartElimArg Raw.ArgSpecExplicit arg : eliminators') ->
      case (_segment'plicity $ binding'segment $ piBinding) of
        Explicit -> apply parent gamma eliminee piBinding arg eliminators' result tyResult
        _ -> autoEliminate parent gamma eliminee tyEliminee eliminators result tyResult Nothing
    -- Immediate application of a function: `f .{arg}` (Apply.)
    (Type (Expr2 (TermCons (ConsUniHS (Pi piBinding)))), SmartElimArg Raw.ArgSpecNext arg : eliminators') ->
      apply parent gamma eliminee piBinding arg eliminators' result tyResult
    -- Named application of a function: `f .{a = arg}` (Apply if the name matches, auto-eliminate otherwise.)
    (Type (Expr2 (TermCons (ConsUniHS (Pi piBinding)))), SmartElimArg (Raw.ArgSpecNamed name) arg : eliminators') ->
      if Just name == (_segment'name $ binding'segment $ piBinding)
      then apply parent gamma eliminee piBinding arg eliminators' result tyResult
      else autoEliminate parent gamma eliminee tyEliminee eliminators result tyResult Nothing
    -- Application of a non-function: `t arg`, `t .{arg}`, `t .{a = arg}` (Auto-eliminate.)
    (_, SmartElimArg _ _ : eliminators') ->
      autoEliminate parent gamma eliminee tyEliminee eliminators result tyResult Nothing
    -- Named projection of a pair: `pair .componentName`
    (Type (Expr2 (TermCons (ConsUniHS (Sigma sigmaBinding)))), SmartElimProj (Raw.ProjSpecNamed name) : eliminators') ->
      -- if the given name is the name of the first component
      if Just name == (_segment'name $ binding'segment $ sigmaBinding)
      -- then project out the first component and continue
      then projFst parent gamma eliminee sigmaBinding eliminators' result tyResult
      -- else project out the second component and try again
      else projSnd parent gamma eliminee sigmaBinding eliminators result tyResult
    -- Numbered projection of a pair: `pair .i`
    (Type (Expr2 (TermCons (ConsUniHS (Sigma sigmaBinding)))), SmartElimProj (Raw.ProjSpecNumbered i) : eliminators') ->
      if i == 1
      -- then project out the first component and continue
      then projFst parent gamma eliminee sigmaBinding eliminators' result tyResult
      -- else project out the second component and decrement
      else let decEliminators = SmartElimProj (Raw.ProjSpecNumbered $ i - 1) : eliminators'
           in  projSnd parent gamma eliminee sigmaBinding decEliminators result tyResult
    -- Numbered tail projection of a pair: `pair ..i`
    (Type (Expr2 (TermCons (ConsUniHS (Sigma sigmaBinding)))), SmartElimProj (Raw.ProjSpecTail i) : eliminators') ->
      if i == 1
      -- then do nothing
      then addNewConstraint
             (JudSmartElim gamma eliminee tyEliminee eliminators' result tyResult)
             (Just parent)
             "Doing nothing."
      -- else project out the second component and decrement
      else let decEliminators = SmartElimProj (Raw.ProjSpecTail $ i - 1) : eliminators'
           in  projSnd parent gamma eliminee sigmaBinding decEliminators result tyResult
    (_, SmartElimProj _ : _) ->
      autoEliminate parent gamma eliminee tyEliminee eliminators result tyResult Nothing

checkSmartElim :: forall sys tc v .
  (SysTC sys, MonadTC sys tc, DeBruijnLevel v) =>
  Constraint sys ->
  Ctx Type sys v Void ->
  Term sys v ->
  Type sys v ->
  [Pair2 ModedModality SmartEliminator sys v] ->
  Term sys v ->
  Type sys v ->
  tc ()
checkSmartElim parent gamma eliminee tyEliminee [] result tyResult =
  checkSmartElimDone parent gamma eliminee tyEliminee result tyResult
checkSmartElim parent gamma eliminee (Type tyEliminee) eliminators result tyResult = do
  let dgamma :: Mode sys v = unVarFromCtx <$> ctx'mode gamma
  let dmuTotal :: ModedModality sys v = concatModedModalityDiagrammatically (fst2 <$> eliminators) dgamma
  (whnTyEliminee, metasTyEliminee) <-
    runWriterT $ whnormalize parent (VarFromCtx <$> dmuTotal :\\ gamma) tyEliminee "Weak-head-normalizing type of eliminee."
  case metasTyEliminee of
    -- the type weak-head-normalizes
    [] -> do
      parent' <- defConstraint
                   (JudSmartElim gamma eliminee (Type whnTyEliminee) eliminators result tyResult)
                   (Just parent)
                   "Weak-head-normalized type."
      checkSmartElimForNormalType parent' gamma eliminee (Type whnTyEliminee) eliminators result tyResult
    -- the type does not weak-head-normalize
    _ -> tcBlock parent "Need to know type in order to make sense of smart-elimination."

