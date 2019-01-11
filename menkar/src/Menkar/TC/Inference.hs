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
import Menkar.TC.Inference.SmartElim
import Menkar.TC.Inference.Rel
import Menkar.TC.Inference.Entry
import Menkar.Fine.WHNormalize

import Data.Void
import Control.Lens
import Data.Functor.Compose
import Control.Monad
import Control.Monad.Writer.Lazy

-- CMODE means you need to check a mode
-- CMODTY means you need to check a modality

-------

checkEtaForNormalType ::
  (MonadTC mode modty rel tc, DeBruijnLevel v) =>
  Constraint mode modty rel ->
  Ctx Type mode modty v Void ->
  Term mode modty v ->
  UniHSConstructor mode modty v ->
  tc ()
checkEtaForNormalType parent gamma t (UniHS _) = return ()
checkEtaForNormalType parent gamma t (Pi piBinding) = do
  let ty = Type $ Expr3 $ TermCons $ ConsUniHS $ Pi piBinding
  body <- newMetaTerm
            (Just parent)
            eqDeg
            (gamma :.. (VarFromCtx <$> binding'segment piBinding))
            (Type $ binding'body piBinding)
            "Infer function body."
  addNewConstraint
    (JudTermRel
      eqDeg
      (duplicateCtx gamma)
      (Pair3 t (Expr3 $ TermCons $ Lam $ Binding (binding'segment piBinding) body))
      (Pair3 ty ty)
    )
    (Just parent)
    "Eta-expand"
checkEtaForNormalType parent gamma t (Sigma sigmaBinding) =
  let dmu = _segment'modty $ binding'segment $ sigmaBinding
  in  if sigmaHasEta dmu (unVarFromCtx <$> ctx'mode gamma)
      then do
        let ty = Type $ Expr3 $ TermCons $ ConsUniHS $ Sigma sigmaBinding
        tmFst <- newMetaTerm
                   (Just parent)
                   eqDeg
                   (VarFromCtx <$> dmu :\\ gamma)
                   (_segment'content $ binding'segment $ sigmaBinding)
                   "Infer first projection."
        tmSnd <- newMetaTerm
                   (Just parent)
                   eqDeg
                   gamma
                   (Type $ substLast3 tmFst $ binding'body sigmaBinding)
                   "Infer second projection."
        addNewConstraint
          (JudTermRel
            eqDeg
            (duplicateCtx gamma)
            (Pair3 t (Expr3 $ TermCons $ Pair sigmaBinding tmFst tmSnd))
            (Pair3 ty ty)
          )
          (Just parent)
          "Eta-expand."
      else return ()
checkEtaForNormalType parent gamma t EmptyType = return ()
checkEtaForNormalType parent gamma t UnitType =
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
checkEtaForNormalType parent gamma t (BoxType segBox) =
  if sigmaHasEta dmu (unVarFromCtx <$> ctx'mode gamma)
  then do
    let ty = Type $ Expr3 $ TermCons $ ConsUniHS $ BoxType segBox
    tmContent <- newMetaTerm
                   (Just parent)
                   eqDeg
                   (VarFromCtx <$> dmu :\\ gamma)
                   (_segment'content segBox)
                   "Infer box content."
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
checkEtaForNormalType parent gamma t NatType = return ()
checkEtaForNormalType parent gamma t (EqType _ _ _) = return ()

checkEta ::
  (MonadTC mode modty rel tc, DeBruijnLevel v) =>
  Constraint mode modty rel ->
  Ctx Type mode modty v Void ->
  Term mode modty v ->
  Type mode modty v ->
  tc ()
checkEta parent gamma t (Type ty) = do
  (whnTy, metas) <- runWriterT $ whnormalize parent gamma ty "Normalizing type."
  case metas of
    [] -> do
      parent' <- defConstraint
                   (JudEta gamma t (Type whnTy))
                   (Just parent)
                   "Weak-head-normalized type."
      case whnTy of
        Var3 v -> return ()
        Expr3 whnTyNV -> case whnTyNV of
          TermCons (ConsUniHS whnTyCons) -> checkEtaForNormalType parent' gamma t whnTyCons
          TermCons _ -> tcFail parent' $ "Type is not a type."
          TermElim _ _ _ _ -> return ()
          TermMeta _ _ -> unreachable
          TermWildcard -> unreachable
          TermQName _ _ -> unreachable
          TermSmartElim _ _ _ -> unreachable
          TermGoal _ _ -> unreachable
          TermProblem _ -> tcFail parent' $ "Nonsensical type."
    _ -> tcBlock parent "Need to weak-head-normalize type before I can eta-expand."

-------
-- ================================================================================================
-------

checkConstraint ::
  (MonadTC mode modty rel tc) =>
  Constraint mode modty rel -> tc ()
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
    {-lvl <- newMetaTerm
             (Just parent)
             topDeg
             (ModedModality dataMode irrMod :\\ gamma)
             (Type $ Expr3 $ TermCons $ ConsUniHS $ NatType)
             "Infer universe level of type."-}
    addNewConstraint
      (JudTerm gamma ty (hs2type $ UniHS (unVarFromCtx <$> ctx'mode gamma) {-lvl-}))
      (Just parent)
      "Checking that type lives in a Hofmann-Streicher universe."

  JudTypeRel deg gamma (Pair3 ty1 ty2) -> checkTypeRel parent deg gamma ty1 ty2

  JudTerm gamma t ty -> checkTerm parent gamma t ty

  JudTermRel deg gamma (Pair3 t1 t2) (Pair3 ty1 ty2) -> checkTermRel parent deg gamma t1 t2 ty1 ty2

  JudEta gamma t tyT -> checkEta parent gamma t tyT

  JudSmartElim gamma dmuElim eliminee tyEliminee eliminators result tyResult ->
    checkSmartElim parent gamma dmuElim eliminee tyEliminee eliminators result tyResult

  -- keep this until the end of time
  JudGoal gamma goalname t tyT -> tcReport parent "This isn't my job; delegating to a human."

  JudResolve gamma t ty -> todo

  JudSegment gamma seg -> checkSegment parent gamma seg

  JudVal gamma val -> checkVal parent gamma val

  JudModule gamma modul -> checkModule parent gamma modul

  JudEntry gamma entry -> checkEntry parent gamma entry
  
  --_ -> _checkConstraint
