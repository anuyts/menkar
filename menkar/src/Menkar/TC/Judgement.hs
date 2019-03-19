module Menkar.TC.Judgement where

import Menkar.System
import Menkar.Fine.Syntax
import Menkar.Basic.Context
import Menkar.Fine.Context
import Menkar.Fine.Judgement
import Menkar.Fine.LookupQName
import qualified Menkar.Raw.Syntax as Raw
import Menkar.Monad.Monad
import Control.Exception.AssertFalse
import Menkar.TC.Term
import Menkar.TC.SmartElim
import Menkar.TC.Rel
import Menkar.TC.Entry
import Menkar.TC.Segment
import Menkar.WHN

import Data.Void
import Control.Lens
import Data.Functor.Compose
import Control.Monad
import Control.Monad.Writer.Lazy

-- CMODE means you need to check a mode
-- CMODTY means you need to check a modality

-------

checkEtaForNormalType :: forall sys tc v .
  (SysTC sys, MonadTC sys tc, DeBruijnLevel v) =>
  Constraint sys ->
  Ctx Type sys v Void ->
  Term sys v ->
  UniHSConstructor sys v ->
  tc ()
checkEtaForNormalType parent gamma t (UniHS _) = return ()
checkEtaForNormalType parent gamma t (Pi piBinding) = do
  let ty = hs2type $ Pi piBinding
  body <- newMetaTerm
            (Just parent)
            --(eqDeg :: Degree sys _)
            (gamma :.. (VarFromCtx <$> binding'segment piBinding))
            (Type $ binding'body piBinding)
            MetaBlocked
            "Infer function body."
  addNewConstraint
    (JudTermRel
      (Eta True)
      (eqDeg :: Degree sys _)
      (duplicateCtx gamma)
      (Twice2 t (Expr2 $ TermCons $ Lam $ Binding (binding'segment piBinding) body))
      (Twice2 ty ty)
    )
    (Just parent)
    "Eta-expand"
checkEtaForNormalType parent gamma t (Sigma sigmaBinding) = do
  let dmu = _segment'modty $ binding'segment $ sigmaBinding
  allowsEta dmu (unVarFromCtx <$> ctx'mode gamma) >>= \ case
    Just True -> do
        let ty = Type $ Expr2 $ TermCons $ ConsUniHS $ Sigma sigmaBinding
        tmFst <- newMetaTerm
                   (Just parent)
                   --(eqDeg :: Degree sys _)
                   (VarFromCtx <$> dmu :\\ gamma)
                   (_segment'content $ binding'segment $ sigmaBinding)
                   MetaBlocked
                   "Infer first projection."
        tmSnd <- newMetaTerm
                   (Just parent)
                   --(eqDeg :: Degree sys _)
                   gamma
                   (Type $ substLast2 tmFst $ binding'body sigmaBinding)
                   MetaBlocked
                   "Infer second projection."
        addNewConstraint
          (JudTermRel
            (Eta True)
            (eqDeg :: Degree sys _)
            (duplicateCtx gamma)
            (Twice2 t (Expr2 $ TermCons $ Pair sigmaBinding tmFst tmSnd))
            (Twice2 ty ty)
          )
          (Just parent)
          "Eta-expand."
    Just False -> return ()
    Nothing -> tcBlock parent "Not sure if this sigma-type has eta."
checkEtaForNormalType parent gamma t EmptyType = return ()
checkEtaForNormalType parent gamma t UnitType =
  let ty = Type $ Expr2 $ TermCons $ ConsUniHS $ UnitType
  in  addNewConstraint
        (JudTermRel
          (Eta True)
          (eqDeg :: Degree sys _)
          (duplicateCtx gamma)
          (Twice2 t (Expr2 $ TermCons $ ConsUnit))
          (Twice2 ty ty)
        )
        (Just parent)
        "Eta-expand"
checkEtaForNormalType parent gamma t (BoxType segBox) = do
  let dmu = _segment'modty $ segBox
  allowsEta dmu (unVarFromCtx <$> ctx'mode gamma) >>= \ case
    Just True -> do
      let ty = Type $ Expr2 $ TermCons $ ConsUniHS $ BoxType segBox
      tmContent <- newMetaTerm
                   (Just parent)
                   --(eqDeg :: Degree sys _)
                   (VarFromCtx <$> dmu :\\ gamma)
                   (_segment'content segBox)
                   MetaBlocked
                   "Infer box content."
      addNewConstraint
        (JudTermRel
          (Eta True)
          (eqDeg :: Degree sys _)
          (duplicateCtx gamma)
          (Twice2 t (Expr2 $ TermCons $ ConsBox segBox tmContent))
          (Twice2 ty ty)
        )
        (Just parent)
        "Eta-expand"
    Just False -> return ()
    Nothing -> tcBlock parent "Not sure if this box-type has eta."
checkEtaForNormalType parent gamma t NatType = return ()
checkEtaForNormalType parent gamma t (EqType _ _ _) = return ()

checkEta ::
  (SysTC sys, MonadTC sys tc, DeBruijnLevel v) =>
  Constraint sys ->
  Ctx Type sys v Void ->
  Term sys v ->
  Type sys v ->
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
        Var2 v -> return ()
        Expr2 whnTyNV -> case whnTyNV of
          TermCons (ConsUniHS whnTyCons) -> checkEtaForNormalType parent' gamma t whnTyCons
          TermCons _ -> tcFail parent' $ "Type is not a type."
          TermElim _ _ _ _ -> return ()
          TermMeta MetaBlocked _ _ _ -> unreachable
          TermMeta MetaNeutral _ _ _ -> tcBlock parent "Need to weak-head-normalize type before I can eta-expand."
          TermWildcard -> unreachable
          TermQName _ _ -> unreachable
          TermAlgorithm _ _ -> unreachable
          TermSys whnSysTy -> checkEtaWHNSysTy parent' gamma t whnSysTy
          TermProblem _ -> tcFail parent' $ "Nonsensical type."
    _ -> tcBlock parent "Need to weak-head-normalize type before I can eta-expand."

-------
-- ================================================================================================
-------

checkConstraint ::
  (SysTC sys, MonadTC sys tc) =>
  Constraint sys -> tc ()
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
             (Type $ Expr2 $ TermCons $ ConsUniHS $ NatType)
             "Infer universe level of type."-}
    addNewConstraint
      (JudTerm gamma ty (hs2type $ UniHS (unVarFromCtx <$> ctx'mode gamma) {-lvl-}))
      (Just parent)
      "Checking that type lives in a Hofmann-Streicher universe."

  JudTypeRel deg gamma (Twice2 ty1 ty2) -> checkTypeRel parent deg gamma ty1 ty2

  JudTerm gamma t ty -> checkTerm parent gamma t ty

  JudTermRel eta deg gamma (Twice2 t1 t2) (Twice2 ty1 ty2) -> checkTermRel parent eta deg gamma t1 t2 ty1 ty2

  JudEta gamma t tyT -> checkEta parent gamma t tyT

  JudSmartElim gamma eliminee tyEliminee eliminators result tyResult ->
    checkSmartElim parent gamma eliminee tyEliminee eliminators result tyResult

  -- keep this until the end of time
  JudGoal gamma goalname t tyT -> tcReport parent "This isn't my job; delegating to a human."

  JudResolve gamma t ty -> todo

  JudMode gamma d -> checkMode parent gamma d
  
  JudModeRel gamma d1 d2 -> checkModeRel parent gamma d1 d2
  
  JudModality gamma mu ddom dcod -> checkModality parent gamma mu ddom dcod
  
  JudModalityRel modrel gamma mu1 mu2 ddom dcod -> checkModalityRel parent modrel gamma mu1 mu2 ddom dcod

  JudModedModality gamma (ModedModality ddom mu) dcod -> do
    addNewConstraint (JudMode gamma ddom) (Just parent) "Checking the mode."
    addNewConstraint (JudModality gamma mu ddom dcod) (Just parent) "Checking the modality."

  JudModedModalityRel modrel gamma (ModedModality ddom1 mu1) (ModedModality ddom2 mu2) dcod -> do
    addNewConstraint (JudModeRel gamma ddom1 ddom2) (Just parent) "Relating modes."
    addNewConstraint (JudModalityRel modrel gamma mu1 mu2 ddom1 dcod) (Just parent) "Relating modalities."

  JudSys jud -> checkSysJudgement parent jud

  JudSegment gamma seg -> checkSegment parent gamma seg

  JudVal gamma val -> checkVal parent gamma val

  JudModule gamma modul -> checkModule parent gamma modul

  JudEntry gamma entry -> checkEntry parent gamma entry
  
  --_ -> _checkConstraint
