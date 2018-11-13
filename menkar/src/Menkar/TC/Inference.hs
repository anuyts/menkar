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

import Data.Void
import Control.Lens
import Data.Functor.Compose
import Control.Monad

-- CMODE means you need to check a mode
-- CMODTY means you need to check a modality

-------

checkPiOrSigma :: MonadTC mode modty rel tc =>
    Constraint mode modty rel ->
    Ctx Type mode modty v Void ->
    Binding Type Term mode modty v ->
    Type mode modty v ->
    tc ()
checkPiOrSigma parent gamma binding ty = do
  -- CMODE
  -- CMODTY
  lvl <- term4newImplicit (ModedModality dataMode irrMod :\\ gamma)
  let currentUni = Type $ Expr3 $ TermCons $ ConsUniHS $ UniHS (unVarFromCtx <$> ctx'mode gamma) lvl
  ---------
  addNewConstraint
    (JudTypeRel
      eqDeg
      (mapCtx (\ty -> Pair3 ty ty) gamma)
      (Pair3 currentUni ty)
    )
    (Just parent)
    "Checking whether actual type equals expected type."
  ----------
  addNewConstraint
    (JudTerm
      ((_segment'modty $ binding'segment $ VarFromCtx <$> binding) :\\ gamma)
      (unType $ _segment'content $ binding'segment $ binding)
      currentUni
    )
    (Just parent)
    "Checking type of the domain."
  ----------
  addNewConstraint
    (JudTerm
      (gamma :.. (VarFromCtx <$> binding'segment binding))
      (binding'body binding)
      (VarWkn <$> currentUni)
    )
    (Just parent)
    "Checking the type of the codomain."

-------

checkUni :: MonadTC mode modty rel tc =>
    Constraint mode modty rel ->
    Ctx Type mode modty v Void ->
    Type mode modty v ->
    tc ()
checkUni parent gamma ty = do
  lvl <- term4newImplicit (ModedModality dataMode irrMod :\\ gamma)
  let currentUni = Type $ Expr3 $ TermCons $ ConsUniHS $ UniHS (unVarFromCtx <$> ctx'mode gamma) lvl
  ---------
  addNewConstraint
    (JudTypeRel
      eqDeg
      (mapCtx (\ty -> Pair3 ty ty) gamma)
      (Pair3 currentUni ty)
    )
    (Just parent)
    "Checking whether actual type equals expected type."

-------

checkConstraintUniHSConstructor :: MonadTC mode modty rel tc =>
    Constraint mode modty rel ->
    Ctx Type mode modty v Void ->
    UniHSConstructor mode modty v ->
    Type mode modty v ->
    tc ()
checkConstraintUniHSConstructor parent gamma (UniHS d lvl) ty = do
  -- CMODE d
  -----
  addNewConstraint
    (JudTerm
      (ModedModality dataMode irrMod :\\ gamma)
      lvl
      (Type $ Expr3 $ TermCons $ ConsUniHS $ NatType)
    )
    (Just parent)
    "Checking the level."
  -----
  anyLvl <- term4newImplicit (ModedModality dataMode irrMod :\\ gamma)
  let biggerLvl =
        -- biggerLvl = suc (lvl + anyLvl)
        Expr3 . TermCons . ConsSuc $
        Expr3 $ TermElim (idModedModality dataMode) lvl (Type $ Expr3 $ TermCons $ ConsUniHS $ NatType) $
        ElimNat
          (NamedBinding Nothing $ Expr3 $ TermCons $ ConsUniHS $ NatType)
          anyLvl
          (NamedBinding Nothing $ NamedBinding (Just $ Raw.Name Raw.NonOp "l")$ Expr3 . TermCons . ConsSuc $ Var3 VarLast)
  addNewConstraint
    (JudTypeRel
      eqDeg
      (mapCtx (\ty -> Pair3 ty ty) gamma)
      (Pair3
        (Type $ Expr3 $ TermCons $ ConsUniHS $ UniHS d biggerLvl)
        ty
      )
    )
    (Just parent)
    "Checking whether actual type equals expected type."
checkConstraintUniHSConstructor parent gamma (Pi binding) ty = checkPiOrSigma parent gamma binding ty
checkConstraintUniHSConstructor parent gamma (Sigma binding) ty = checkPiOrSigma parent gamma binding ty
checkConstraintUniHSConstructor parent gamma (EmptyType) ty = checkUni parent gamma ty
checkConstraintUniHSConstructor parent gamma (UnitType) ty = checkUni parent gamma ty
checkConstraintUniHSConstructor parent gamma (BoxType seg) ty = do
  lvl <- term4newImplicit (ModedModality dataMode irrMod :\\ gamma)
  let currentUni = Type $ Expr3 $ TermCons $ ConsUniHS $ UniHS (unVarFromCtx <$> ctx'mode gamma) lvl
  ---------
  addNewConstraint
    (JudTypeRel
      eqDeg
      (mapCtx (\ty -> Pair3 ty ty) gamma)
      (Pair3 currentUni ty)
    )
    (Just parent)
    "Checking whether actual type equals expected type."
  ----------
  addNewConstraint
    (JudTerm
      ((_segment'modty $ VarFromCtx <$> seg) :\\ gamma)
      (unType $ _segment'content $ seg)
      currentUni
    )
    (Just parent)
    "Checking type of the inner type."
checkConstraintUniHSConstructor parent gamma (NatType) ty = checkUni parent gamma ty
--checkConstraintUniHSConstructor parent gamma t ty = _checkConstraintUniHSConstructor
-- CMODE do we allow Empty, Unit and Nat in arbitrary mode? I guess not...

checkConstraintConstructorTerm :: MonadTC mode modty rel tc =>
    Constraint mode modty rel ->
    Ctx Type mode modty v Void ->
    ConstructorTerm mode modty v ->
    Type mode modty v ->
    tc ()
checkConstraintConstructorTerm parent gamma (ConsUniHS t) ty = checkConstraintUniHSConstructor parent gamma t ty
checkConstraintConstructorTerm parent gamma (Lam binding) ty = do
  -- CMODE
  -- CMODTY
  ----------
  addNewConstraint
    (JudType
      ((_segment'modty $ binding'segment $ VarFromCtx <$> binding) :\\ gamma)
      (_segment'content $ binding'segment $ binding)
    )
    (Just parent)
    "Checking the domain."
  ----------
  codomain <- term4newImplicit (gamma :.. (VarFromCtx <$> binding'segment binding))
  addNewConstraint
    (JudTerm
      (gamma :.. (VarFromCtx <$> binding'segment binding))
      (binding'body binding)
      (Type codomain)
    )
    (Just parent)
    "Type-checking the body."
  ----------
  addNewConstraint
    (JudTypeRel
      eqDeg
      (mapCtx (\ty -> Pair3 ty ty) gamma)
      (Pair3
        (Type $ Expr3 $ TermCons $ ConsUniHS $ Pi $ Binding (binding'segment binding) codomain)
        ty
      )
    )
    (Just parent)
    "Checking whether actual type equals expected type."
checkConstraintConstructorTerm parent gamma (Pair sigmaBinding t1 t2) ty = do
  let sigmaType = Type $ Expr3 $ TermCons $ ConsUniHS $ Sigma sigmaBinding
  ----------
  addNewConstraint
    (JudType gamma sigmaType)
    (Just parent)
    "Checking the type"
  ----------
  addNewConstraint
    (JudTerm
      ((_segment'modty $ binding'segment $ VarFromCtx <$> sigmaBinding) :\\ gamma)
      t1
      (_segment'content $ binding'segment $ sigmaBinding)
    )
    (Just parent)
    "Type-checking first component."
  ----------
  let subst :: VarExt _ -> Term _ _ _
      subst VarLast = t1
      subst (VarWkn v) = Var3 v
      subst v = unreachable
  addNewConstraint
    (JudTerm gamma t2 (Type $ join $ subst <$> binding'body sigmaBinding))
    (Just parent)
    "Type-checking second component."
  ----------
  addNewConstraint
    (JudTypeRel
      eqDeg
      (mapCtx (\ty -> Pair3 ty ty) gamma)
      (Pair3 sigmaType ty)
    )
    (Just parent)
    "Checking whether actual type equals expected type."
checkConstraintConstructorTerm parent gamma ConsUnit ty = do
  -- CMODE
  ----------
  addNewConstraint
    (JudTypeRel
      eqDeg
      (mapCtx (\ty -> Pair3 ty ty) gamma)
      (Pair3 (Type $ Expr3 $ TermCons $ ConsUniHS $ UnitType) ty)
    )
    (Just parent)
    "Checking whether actual type equals expected type."
checkConstraintConstructorTerm parent gamma (ConsBox typeSegment t) ty = do
  let boxType = Type $ Expr3 $ TermCons $ ConsUniHS $ BoxType typeSegment
  ----------
  addNewConstraint
    (JudType gamma boxType)
    (Just parent)
    "Checking the type"
  ----------
  addNewConstraint
    (JudTerm
      ((_segment'modty $ VarFromCtx <$> typeSegment) :\\ gamma)
      t
      (_segment'content $ typeSegment)
    )
    (Just parent)
    "Type-checking box content."
  ----------
  addNewConstraint
    (JudTypeRel
      eqDeg
      (mapCtx (\ty -> Pair3 ty ty) gamma)
      (Pair3 boxType ty)
    )
    (Just parent)
    "Checking whether actual type equals expected type."
checkConstraintConstructorTerm parent gamma ConsZero ty = do
  -- CMODE
  ----------
  addNewConstraint
    (JudTypeRel
      eqDeg
      (mapCtx (\ty -> Pair3 ty ty) gamma)
      (Pair3 (Type $ Expr3 $ TermCons $ ConsUniHS $ NatType) ty)
    )
    (Just parent)
    "Checking whether actual type equals expected type."
checkConstraintConstructorTerm parent gamma (ConsSuc t) ty = do
  -- CMODE
  ----------
  addNewConstraint
    (JudTerm gamma t (Type $ Expr3 $ TermCons $ ConsUniHS $ NatType))
    (Just parent)
    "Type-checking predecessor."
  ----------
  addNewConstraint
    (JudTypeRel
      eqDeg
      (mapCtx (\ty -> Pair3 ty ty) gamma)
      (Pair3 (Type $ Expr3 $ TermCons $ ConsUniHS $ NatType) ty)
    )
    (Just parent)
    "Checking whether actual type equals expected type."
--checkConstraintConstructorTerm parent gamma c (Type ty) = _checkConstraintConstructorTerm

-------

checkConstraintEliminator :: MonadTC mode modty rel tc =>
    Constraint mode modty rel ->
    Ctx Type mode modty v Void ->
    ModedModality mode modty v ->
    Term mode modty v ->
    Type mode modty v ->
    Eliminator mode modty v ->
    Type mode modty v ->
    tc ()
checkConstraintEliminator parent gamma dmu eliminee (Type (Expr3 (TermCons (ConsUniHS (Pi binding))))) (App arg) ty = do
  let dmu = _segment'modty $ binding'segment $ binding
  let dom = _segment'content $ binding'segment binding
  addNewConstraint
    (JudTerm ((VarFromCtx <$> dmu) :\\ gamma) arg dom)
    (Just parent)
    "Type-checking argument."
  let subst :: VarExt _ -> Term _ _ _
      subst VarLast = arg
      subst (VarWkn v) = Var3 v
      subst _ = unreachable
  addNewConstraint
    (JudTypeRel
      eqDeg
      (mapCtx (\ty -> Pair3 ty ty) gamma)
      (Pair3
        (Type $ join $ subst <$> binding'body binding)
        ty
      )
    )
    (Just parent)
    "Checking whether actual type equals expected type."
checkConstraintEliminator parent gamma dmu eliminee tyEliminee (App arg) ty = unreachable
-- dependent elims: type-check motive and take them separately
checkConstraintEliminator parent gamma dmu eliminee tyEliminee eliminator ty = _checkConstraintEliminator

-------
    
checkConstraintTermNV :: MonadTC mode modty rel tc =>
    Constraint mode modty rel ->
    Ctx Type mode modty v Void ->
    TermNV mode modty v ->
    Type mode modty v ->
    tc ()
checkConstraintTermNV parent gamma (TermCons c) ty = checkConstraintConstructorTerm parent gamma c ty
checkConstraintTermNV parent gamma (TermElim dmu eliminee tyEliminee eliminator) ty = do
  -- CMODE CMODTY
  addNewConstraint
    (JudType ((VarFromCtx <$> dmu) :\\ gamma) tyEliminee)
    (Just parent)
    "Checking type of eliminee."
  addNewConstraint
    (JudTerm ((VarFromCtx <$> dmu) :\\ gamma) eliminee tyEliminee)
    (Just parent)
    "Type-checking eliminee."
  checkConstraintEliminator parent gamma dmu eliminee tyEliminee eliminator ty
checkConstraintTermNV parent gamma t@(TermMeta meta (Compose depcies)) ty = do
  maybeT <- getMeta meta depcies
  case maybeT of
    Nothing -> do
      {-addNewConstraint
        (JudEta gamma (Expr3 t) ty)
        (Just parent)
        "Eta-expand meta if possible."
      -}
      blockOnMetas [meta] parent
    Just t' -> do
      i <- newConstraintID
      checkConstraint $ Constraint
        (JudTerm gamma t' ty)
        (Just parent)
        "Look up meta."
        i
checkConstraintTermNV parent gamma (TermQName qname lookupresult) (Type ty) = do
  let ldivModAppliedVal = VarFromCtx <$> over leftDivided'content telescoped2modalQuantified lookupresult
  varAccessible <- leqMod
        (modality'mod . _modApplied'modality . _leftDivided'content $ ldivModAppliedVal)
        (modality'mod . _leftDivided'modality $ ldivModAppliedVal)
  if varAccessible
        then do
          addNewConstraint
            (JudTypeRel
              eqDeg
              (mapCtx (\ty -> Pair3 ty ty) gamma)
              (Pair3
                (unVarFromCtx <$> (_val'type . _modApplied'content . _leftDivided'content $ ldivModAppliedVal))
                (Type ty)
              )
            )
            (Just parent)
            "Checking whether actual type equals expected type."
        else tcFail parent $ "Object cannot be used here: modality restrictions are too strong."
checkConstraintTermNV parent gamma (TermSmartElim eliminee (Compose eliminators) result) ty = do
  tyEliminee <- Type <$> term4newImplicit gamma
  -----
  addNewConstraint
    (JudTerm gamma eliminee tyEliminee)
    (Just parent)
    "Type-check the eliminee"
  -----
  addNewConstraint
    (JudTerm gamma result ty)
    (Just parent)
    "Smart elimination should reduce to value of the appropriate type."
  -----
  addNewConstraint
    (JudSmartElim gamma eliminee tyEliminee eliminators result)
    (Just parent)
    "Smart elimination should reduce to its result."
checkConstraintTermNV parent gamma (TermGoal goalname result) ty = do
  -----
  addNewConstraint
    (JudTerm gamma result ty)
    (Just parent)
    "Goal should take value of the appropriate type."
  -----
  j <- newConstraintID
  blockOnMetas [] $ Constraint
      (JudGoal gamma goalname result ty)
      (Just parent)
      "Goal should take some value."
      j
checkConstraintTermNV parent gamma (TermProblem t) (Type ty) = tcFail parent $ "Erroneous term."

-------

checkConstraintTerm :: MonadTC mode modty rel tc =>
    Constraint mode modty rel ->
    Ctx Type mode modty v Void ->
    Term mode modty v ->
    Type mode modty v ->
    tc ()
checkConstraintTerm parent gamma (Var3 v) (Type ty) = do
  let ldivSeg = lookupVar gamma v
  varAccessible <- leqMod
    (modality'mod . _decl'modty . _leftDivided'content $ ldivSeg)
    (modality'mod . _leftDivided'modality $ ldivSeg)
  if varAccessible
    then do
      addNewConstraint
        (JudTypeRel
          eqDeg
          (mapCtx (\ty -> Pair3 ty ty) gamma)
          (Pair3
            (unVarFromCtx <$> (_decl'content . _leftDivided'content $ ldivSeg))
            (Type ty)
          )
        )
        (Just parent)
        "Checking whether actual type equals expected type."
    else tcFail parent $ "Variable cannot be used here: modality restrictions are too strong."
checkConstraintTerm parent gamma (Expr3 t) ty = checkConstraintTermNV parent gamma t ty

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

  JudTerm gamma t ty -> checkConstraintTerm parent gamma t ty
  
  _ -> _checkConstraint
