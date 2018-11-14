module Menkar.TC.Inference where

import Menkar.Fine.Syntax
import Menkar.Basic.Context
import Menkar.Fine.Context
import Menkar.Fine.Judgement
import Menkar.Fine.Multimode
import Menkar.Fine.LookupQName
import qualified Menkar.Raw.Syntax as Raw
import Menkar.TC.Monad
import Control.Exception.AssertFalse
import Menkar.TC.Inference.Term
import Menkar.Fine.WHNormalize

import Data.Void
import Control.Lens
import Data.Functor.Compose
import Control.Monad
import Control.Monad.Writer.Lazy

-- CMODE means you need to check a mode
-- CMODTY means you need to check a modality

-------

checkEtaType :: (MonadTC mode modty rel tc) =>
  Constraint mode modty rel ->
  Ctx Type mode modty v Void ->
  Term mode modty v ->
  UniHSConstructor mode modty v ->
  tc ()
checkEtaType parent gamma t (UniHS _ _) = return ()
checkEtaType parent gamma t (Pi piBinding) = do
  let ty = Type $ Expr3 $ TermCons $ ConsUniHS $ Pi piBinding
  body <- term4newImplicit (gamma :.. (VarFromCtx <$> binding'segment piBinding))
  addNewConstraint
    (JudTermRel
      eqDeg
      (duplicateCtx gamma)
      (Pair3 t (Expr3 $ TermCons $ Lam $ Binding (binding'segment piBinding) body))
      (Pair3 ty ty)
    )
    (Just parent)
    "Eta-expand"
checkEtaType parent gamma t (Sigma sigmaBinding) =
  if sigmaHasEta dmu (unVarFromCtx <$> ctx'mode gamma)
  then do
    let ty = Type $ Expr3 $ TermCons $ ConsUniHS $ Sigma sigmaBinding
    tmFst <- term4newImplicit (VarFromCtx <$> dmu :\\ gamma)
    tmSnd <- term4newImplicit gamma
    addNewConstraint
      (JudTermRel
        eqDeg
        (duplicateCtx gamma)
        (Pair3 t (Expr3 $ TermCons $ Pair sigmaBinding tmFst tmSnd))
        (Pair3 ty ty)
      )
      (Just parent)
      "Eta-expand"
  else return ()
  where dmu = _segment'modty $ binding'segment $ sigmaBinding
checkEtaType parent gamma t EmptyType = return ()
checkEtaType parent gamma t UnitType =
  let ty = Type $ Expr3 $ TermCons $ ConsUniHS $ UnitType
  in  addNewConstraint
        (JudTermRel
          eqDeg
          (duplicateCtx gamma)
          (Pair3 t (Expr3 $ TermCons $ ConsUnit))
          (Pair3 ty ty)
        )
        (Just parent)
        "Eta-expand"
checkEtaType parent gamma t (BoxType segBox) =
  if sigmaHasEta dmu (unVarFromCtx <$> ctx'mode gamma)
  then do
    let ty = Type $ Expr3 $ TermCons $ ConsUniHS $ BoxType segBox
    tmContent <- term4newImplicit (VarFromCtx <$> dmu :\\ gamma)
    addNewConstraint
      (JudTermRel
        eqDeg
        (duplicateCtx gamma)
        (Pair3 t (Expr3 $ TermCons $ ConsBox segBox tmContent))
        (Pair3 ty ty)
      )
      (Just parent)
      "Eta-expand"
  else return ()
  where dmu = _segment'modty $ segBox
checkEtaType parent gamma t NatType = return ()

checkEta :: (MonadTC mode modty rel tc) =>
  Constraint mode modty rel ->
  Ctx Type mode modty v Void ->
  Term mode modty v ->
  Type mode modty v ->
  tc ()
checkEta parent gamma t (Type ty) = do
  (whTy, metas) <- runWriterT $ whnormalize gamma ty
  case metas of
    [] -> do
      parent' <- Constraint
                   (JudEta gamma t (Type whTy))
                   (Just parent)
                   "Weak-head-normalized type."
                   <$> newConstraintID
      case whTy of
        Var3 v -> return ()
        Expr3 whTyNV -> case whTyNV of
          TermCons (ConsUniHS whTyCons) -> checkEtaType parent' gamma t whTyCons
          TermCons _ -> tcFail parent' $ "Type is not a type."
          TermElim _ _ _ _ -> return ()
          TermMeta _ _ -> unreachable
          TermQName _ _ -> unreachable
          TermSmartElim _ _ _ -> unreachable
          TermGoal _ _ -> unreachable
          TermProblem _ -> tcFail parent' $ "Nonsensical type."
    _ -> blockOnMetas metas parent
    
-------

checkSmartElim :: (MonadTC mode modty rel tc) =>
  Constraint mode modty rel ->
  Ctx Type mode modty v Void ->
  Term mode modty v ->
  Type mode modty v ->
  [SmartEliminator mode modty v] ->
  Term mode modty v ->
  tc ()
checkSmartElim parent gamma eliminee (Type tyEliminee) eliminators result = do
  (whTyEliminee, metas) <- runWriterT $ whnormalize gamma tyEliminee
  case metas of
    [] -> do
      parent' <- Constraint
                   (JudSmartElim gamma eliminee (Type whTyEliminee) eliminators result)
                   (Just parent)
                   "Weak-head-normalized type."
                   <$> newConstraintID
      _checkSmartElim
    _ -> blockOnMetas metas parent

-------
-- ================================================================================================
-------

checkConstraint :: (MonadTC mode modty rel tc) => Constraint mode modty rel -> tc ()

checkConstraint parent = case constraint'judgement parent of
  
  {-
  JudCtx gamma d -> case gamma of
    CtxEmpty -> return ()
    gamma2 :.. seg -> do
      let ty = _decl'content seg
      let ModedModality d2 mu = _decl'modty seg
      let gamma3 = ModedContramodality d mu :\\ gamma2
      i <- newConstraintID
      -- CMODE b\gamma d2
      -- CMODTY b\gamma mu
      addConstraint $ Constraint
            (JudType gamma3 d2 ty)
            constraint
            "Checking type of last variable in context."
            i
    seg :^^ gamma2 -> tcFail $ "For now, left extension of context is not supported by the type-checker."
    gamma2 :<...> modul -> 
    _ -> _checkJudCtx
  -} -- contexts start empty and grow only in well-typed ways.

  JudType gamma (Type ty) -> do
    lvl <- term4newImplicit gamma
    addNewConstraint
      (JudTerm gamma ty (Type $ Expr3 $ TermCons $ ConsUniHS $ UniHS (unVarFromCtx <$> ctx'mode gamma) lvl))
      (Just parent)
      "Checking that type lives in a Hofmann-Streicher universe."

  JudTerm gamma t ty -> checkTerm parent gamma t ty

  JudEta gamma t tyT -> checkEta parent gamma t tyT

  JudSmartElim gamma eliminee tyEliminee eliminators result ->
    checkSmartElim parent gamma eliminee tyEliminee eliminators result

  -- keep this until the end of time
  JudGoal gamma goalname t tyT -> blockOnMetas [] parent

  JudResolve gamma t ty -> unreachable
  
  _ -> _checkConstraint
