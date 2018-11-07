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

-- CMODE means you need to check a mode
-- CMODTY means you need to check a modality

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
  j <- newConstraintID
  addConstraint $ Constraint
    (JudTerm
      (ModedModality dataMode irrMod :\\ gamma)
      lvl
      (Type $ Expr3 $ TermCons $ ConsUniHS $ NatType)
    )
    (Just parent)
    "Checking the level."
    j
  -----
  anyLvl <- term4newImplicit (ModedModality dataMode irrMod :\\ gamma)
  let biggerLvl =
        -- biggerLvl = suc (lvl + anyLvl)
        Expr3 . TermCons . ConsSuc $
        Expr3 $ TermElim (idModedModality dataMode) lvl $
        ElimNat
          (Expr3 $ TermCons $ ConsUniHS $ NatType)
          anyLvl
          (Expr3 . TermCons . ConsSuc $ Var3 VarLast)
  i <- newConstraintID
  addConstraint $ Constraint
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
    i
checkConstraintUniHSConstructor parent gamma (Pi binding) ty = _ --do
  --lvl <- term4newImplicit
checkConstraintUniHSConstructor parent gamma t ty = _checkConstraintUniHSConstructor

checkConstraintConstructorTerm :: MonadTC mode modty rel tc =>
    Constraint mode modty rel ->
    Ctx Type mode modty v Void ->
    ConstructorTerm mode modty v ->
    Type mode modty v ->
    tc ()
checkConstraintConstructorTerm parent gamma (ConsUniHS t) ty = checkConstraintUniHSConstructor parent gamma t ty
checkConstraintConstructorTerm parent gamma c (Type ty) = _checkConstraintConstructorTerm
{-checkConstraintConstructorTerm parent gamma (Lam binding) ty = do
  tDom <- term4newImplicit gamma
  let seg = _ $ binding'segment binding
  i <- newConstraintID
  _-}

-------
    
checkConstraintTermNV :: MonadTC mode modty rel tc =>
    Constraint mode modty rel ->
    Ctx Type mode modty v Void ->
    TermNV mode modty v ->
    Type mode modty v ->
    tc ()
checkConstraintTermNV parent gamma (TermCons c) ty = checkConstraintConstructorTerm parent gamma c ty
checkConstraintTermNV parent gamma (TermElim dmu eliminee eliminator) (Type ty) = _checkConstraintTermElim
checkConstraintTermNV parent gamma (TermMeta meta (Compose depcies)) ty = do
  maybeT <- getMeta meta depcies
  case maybeT of
    Nothing -> blockOnMetas [meta] parent
    Just t -> do
      i <- newConstraintID
      checkConstraint $ Constraint
        (JudTerm gamma t ty)
        (Just parent)
        "Look up meta."
        i
checkConstraintTermNV parent gamma (TermQName qname) (Type ty) =
  case over leftDivided'content telescoped2modalQuantified <$> lookupQName gamma qname of
    Nothing -> tcFail parent $ "Not in scope (or misspelled)."
    Just ldivModAppliedVal -> do
      varAccessible <- leqMod
        (modality'mod . _modApplied'modality . _leftDivided'content $ ldivModAppliedVal)
        (modality'mod . _leftDivided'modality $ ldivModAppliedVal)
      if varAccessible
        then do
          i <- newConstraintID
          addConstraint $ Constraint
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
            i
        else tcFail parent $ "Object cannot be used here: modality restrictions are too strong."
checkConstraintTermNV parent gamma (TermSmartElim eliminee (Compose eliminators) result) ty = do
  tyEliminee <- Type <$> term4newImplicit gamma
  -----
  k <- newConstraintID
  addConstraint $ Constraint
    (JudTerm gamma eliminee tyEliminee)
    (Just parent)
    "Type-check the eliminee"
    k
  -----
  i <- newConstraintID
  addConstraint $ Constraint
    (JudTerm gamma result ty)
    (Just parent)
    "Smart elimination should reduce to value of the appropriate type."
    i
  -----
  j <- newConstraintID
  addConstraint $ Constraint
    (JudSmartElim gamma eliminee tyEliminee eliminators result)
    (Just parent)
    "Smart elimination should reduce to its result."
    j
checkConstraintTermNV parent gamma (TermGoal goalname result) ty = do
  -----
  i <- newConstraintID
  addConstraint $ Constraint
    (JudTerm gamma result ty)
    (Just parent)
    "Goal should take value of the appropriate type."
    i
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
      i <- newConstraintID
      addConstraint $ Constraint
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
        i
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
    i <- newConstraintID
    addConstraint $ Constraint
      (JudTerm gamma ty (Type $ Expr3 $ TermCons $ ConsUniHS $ UniHS (unVarFromCtx <$> ctx'mode gamma) lvl))
      (Just parent)
      "Checking that type lives in a Hofmann-Streicher universe."
      i

  JudTerm gamma t ty -> checkConstraintTerm parent gamma t ty
  
  _ -> _checkConstraint
