module Menkar.TC.Inference.Term where

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

checkPiOrSigma ::
    (MonadTC mode modty rel tc, DeBruijnLevel v) =>
    Constraint mode modty rel ->
    Ctx Type mode modty v Void ->
    Binding Type Term mode modty v ->
    Type mode modty v ->
    tc ()
checkPiOrSigma parent gamma binding ty = do
  -- CMODE
  -- CMODTY
  lvl <- newMetaTerm
           (Just parent)
           topDeg
           (ModedModality dataMode irrMod :\\ gamma)
           (Type $ Expr3 $ TermCons $ ConsUniHS $ NatType)
           "Infer level."
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

checkUni ::
    (MonadTC mode modty rel tc, DeBruijnLevel v) =>
    Constraint mode modty rel ->
    Ctx Type mode modty v Void ->
    Type mode modty v ->
    tc ()
checkUni parent gamma ty = do
  lvl <- newMetaTerm
           (Just parent)
           topDeg
           (ModedModality dataMode irrMod :\\ gamma)
           (Type $ Expr3 $ TermCons $ ConsUniHS $ NatType)
           "Infer level."
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

checkUniHSConstructor ::
    (MonadTC mode modty rel tc, DeBruijnLevel v) =>
    Constraint mode modty rel ->
    Ctx Type mode modty v Void ->
    UniHSConstructor mode modty v ->
    Type mode modty v ->
    tc ()
checkUniHSConstructor parent gamma (UniHS d lvl) ty = do
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
  anyLvl <- newMetaTerm
           (Just parent)
           topDeg
           (ModedModality dataMode irrMod :\\ gamma)
           (Type $ Expr3 $ TermCons $ ConsUniHS $ NatType)
           ("Inferring some level. The level of the universe we're checking, " ++
           "plus this level, plus 1 is the level of the containing universe.")
  let biggerLvl =
        -- biggerLvl = suc (lvl + anyLvl)
        Expr3 . TermCons . ConsSuc $
        Expr3 $ TermElim (idModedModality dataMode) lvl NatType $
        ElimDep (NamedBinding Nothing $ Type $ Expr3 $ TermCons $ ConsUniHS $ NatType) $
        ElimNat
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
checkUniHSConstructor parent gamma (Pi binding) ty = checkPiOrSigma parent gamma binding ty
checkUniHSConstructor parent gamma (Sigma binding) ty = checkPiOrSigma parent gamma binding ty
checkUniHSConstructor parent gamma (EmptyType) ty = checkUni parent gamma ty
checkUniHSConstructor parent gamma (UnitType) ty = checkUni parent gamma ty
checkUniHSConstructor parent gamma (BoxType seg) ty = do
  lvl <- newMetaTerm
           (Just parent)
           topDeg
           (ModedModality dataMode irrMod :\\ gamma)
           (Type $ Expr3 $ TermCons $ ConsUniHS $ NatType)
           "Infer level."
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
checkUniHSConstructor parent gamma (NatType) ty = checkUni parent gamma ty
--checkUniHSConstructor parent gamma t ty = _checkUniHSConstructor
-- CMODE do we allow Empty, Unit and Nat in arbitrary mode? I guess not...

checkConstructorTerm ::
    (MonadTC mode modty rel tc, DeBruijnLevel v) =>
    Constraint mode modty rel ->
    Ctx Type mode modty v Void ->
    ConstructorTerm mode modty v ->
    Type mode modty v ->
    tc ()
checkConstructorTerm parent gamma (ConsUniHS t) ty = checkUniHSConstructor parent gamma t ty
checkConstructorTerm parent gamma (Lam binding) ty = do
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
  codomain <- newMetaType
                (Just parent)
                eqDeg
                (gamma :.. (VarFromCtx <$> binding'segment binding))
                "Inferring codomain."
  addNewConstraint
    (JudTerm
      (gamma :.. (VarFromCtx <$> binding'segment binding))
      (binding'body binding)
      codomain
    )
    (Just parent)
    "Type-checking the body."
  ----------
  addNewConstraint
    (JudTypeRel
      eqDeg
      (mapCtx (\ty -> Pair3 ty ty) gamma)
      (Pair3
        (Type $ Expr3 $ TermCons $ ConsUniHS $ Pi $ Binding (binding'segment binding) $ unType codomain)
        ty
      )
    )
    (Just parent)
    "Checking whether actual type equals expected type."
checkConstructorTerm parent gamma (Pair sigmaBinding t1 t2) ty = do
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
checkConstructorTerm parent gamma ConsUnit ty = do
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
checkConstructorTerm parent gamma (ConsBox typeSegment t) ty = do
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
checkConstructorTerm parent gamma ConsZero ty = do
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
checkConstructorTerm parent gamma (ConsSuc t) ty = do
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
--checkConstructorTerm parent gamma c (Type ty) = _checkConstructorTerm

-------

checkDependentEliminator :: forall mode modty rel tc v .
    (MonadTC mode modty rel tc, DeBruijnLevel v) =>
    Constraint mode modty rel ->
    Ctx Type mode modty v Void ->
    ModedModality mode modty v ->
    Term mode modty v ->
    UniHSConstructor mode modty v ->
    NamedBinding Type mode modty v ->
    DependentEliminator mode modty v ->
    Type mode modty v ->
    tc ()
checkDependentEliminator parent gamma dmu eliminee
    tyEliminee@(Sigma sigmaBinding) motive (ElimSigma clause) ty = do
  let segFst :: Segment Type _ _ _
      segFst = Declaration
                 (DeclNameSegment $ _namedBinding'name clause)
                 (compModedModality dmu (_segment'modty $ binding'segment $ sigmaBinding))
                 Explicit
                 (_segment'content $ binding'segment $ sigmaBinding)
  let segSnd :: Segment Type _ _ (VarExt _)
      segSnd = Declaration
                 (DeclNameSegment $ _namedBinding'name $ _namedBinding'body clause)
                 (VarWkn <$> dmu)
                 Explicit
                 (Type $ binding'body sigmaBinding)
  let subst :: VarExt _ -> Term _ _ (VarExt (VarExt _))
      subst VarLast = Expr3 $ TermCons $ Pair (VarWkn . VarWkn <$> sigmaBinding) (Var3 $ VarWkn VarLast) (Var3 VarLast)
      subst (VarWkn v) = Var3 $ VarWkn $ VarWkn v
  addNewConstraint
    (JudTerm
      (gamma :.. (VarFromCtx <$> segFst) :.. (VarFromCtx <$> segSnd))
      (_namedBinding'body $ _namedBinding'body $ clause)
      (swallow $ subst <$> (_namedBinding'body motive))
    )
    (Just parent)
    "Type-checking pair clause."
checkDependentEliminator parent gamma dmu eliminee
    tyEliminee motive (ElimSigma clause) ty = unreachable
checkDependentEliminator parent gamma dmu eliminee
    tyEliminee@(BoxType boxSeg) motive (ElimBox clause) ty = do
  let segContent :: Segment Type _ _ _
      segContent = Declaration
                     (DeclNameSegment $ _namedBinding'name clause)
                     (compModedModality dmu (_segment'modty boxSeg))
                     Explicit
                     (_segment'content boxSeg)
  let subst :: VarExt _ -> Term _ _ (VarExt _)
      subst VarLast = Expr3 $ TermCons $ ConsBox (VarWkn <$> boxSeg) $ Var3 VarLast
      subst (VarWkn v) = Var3 $ VarWkn v
  addNewConstraint
    (JudTerm
      (gamma :.. (VarFromCtx <$> segContent))
      (_namedBinding'body $ clause)
      (swallow $ subst <$> (_namedBinding'body motive))
    )
    (Just parent)
    "Type-checking box clause."
checkDependentEliminator parent gamma dmu eliminee
    tyEliminee motive (ElimBox clause) ty = unreachable
checkDependentEliminator parent gamma dmu eliminee
    EmptyType motive (ElimEmpty) ty = return ()
checkDependentEliminator parent gamma dmu eliminee
    tyEliminee motive (ElimEmpty) ty = unreachable
checkDependentEliminator parent gamma dmu eliminee
    NatType motive (ElimNat cz cs) ty = do
  let substZ :: VarExt v -> Term mode modty v
      substZ VarLast = Expr3 $ TermCons $ ConsZero
      substZ (VarWkn v) = Var3 v
  addNewConstraint
    (JudTerm gamma cz (swallow $ substZ <$> _namedBinding'body motive))
    (Just parent)
    "Type-checking zero clause."
  let segPred :: Segment Type _ _ _
      segPred = Declaration
                  (DeclNameSegment $ _namedBinding'name cs)
                  dmu
                  Explicit
                  (Type $ Expr3 $ TermCons $ ConsUniHS $ NatType)
  let segHyp :: Segment Type _ _ (VarExt _)
      segHyp = Declaration
                  (DeclNameSegment $ _namedBinding'name $ _namedBinding'body cs)
                  (idModedModality $ VarWkn . unVarFromCtx <$> ctx'mode gamma)
                  Explicit
                  (_namedBinding'body motive)
  let substS :: VarExt v -> Term mode modty (VarExt (VarExt v))
      substS VarLast = Expr3 $ TermCons $ ConsSuc $ Var3 $ VarWkn VarLast
      substS (VarWkn v) = Var3 $ VarWkn $ VarWkn v
  addNewConstraint
    (JudTerm
      (gamma :.. (VarFromCtx <$> segPred) :.. (VarFromCtx <$> segHyp))
      (_namedBinding'body $ _namedBinding'body $ cs)
      (swallow $ substS <$> _namedBinding'body motive)
    )
    (Just parent)
    "Type-checking successor clause."
checkDependentEliminator parent gamma dmu eliminee
    tyEliminee motive (ElimNat cz cs) ty = unreachable

-------

checkEliminator ::
    (MonadTC mode modty rel tc, DeBruijnLevel v) =>
    Constraint mode modty rel ->
    Ctx Type mode modty v Void ->
    ModedModality mode modty v ->
    Term mode modty v ->
    UniHSConstructor mode modty v ->
    Eliminator mode modty v ->
    Type mode modty v ->
    tc ()
checkEliminator parent gamma dmu eliminee (Pi binding) (App arg) ty = do
  let dmu = _segment'modty $ binding'segment $ binding
  let dom = _segment'content $ binding'segment binding
  addNewConstraint
    (JudTerm ((VarFromCtx <$> dmu) :\\ gamma) arg dom)
    (Just parent)
    "Type-checking argument."
  let subst :: VarExt _ -> Term _ _ _
      subst VarLast = arg
      subst (VarWkn v) = Var3 v
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
checkEliminator parent gamma dmu eliminee tyEliminee (App arg) ty = unreachable
checkEliminator parent gamma dmu eliminee (Sigma binding) Fst ty = do
  addNewConstraint
    (JudTypeRel
      eqDeg
      (mapCtx (\ty -> Pair3 ty ty) gamma)
      (Pair3
        (_segment'content $ binding'segment binding)
        ty
      )
    )
    (Just parent)
    "Checking whether actual type equals expected type."
checkEliminator parent gamma dmu eliminee tyEliminee Fst ty = unreachable
checkEliminator parent gamma dmu eliminee
    tyEliminee@(Sigma binding) Snd ty = do
  let dFst = modality'dom $ _segment'modty $ binding'segment $ binding
      muSigma = modality'mod $ _segment'modty $ binding'segment $ binding
      dSnd = unVarFromCtx <$> ctx'mode gamma
      muProj = approxLeftAdjointProj (ModedModality dFst muSigma) dSnd
      subst :: VarExt _ -> Term _ _ _
      subst VarLast = Expr3 $ TermElim (ModedModality dSnd muProj) eliminee tyEliminee Fst
      subst (VarWkn v) = Var3 v
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
checkEliminator parent gamma dmu eliminee tyEliminee Snd ty = unreachable
checkEliminator parent gamma dmu eliminee
    tyEliminee@(BoxType segment) Unbox ty = do
  addNewConstraint
    (JudTypeRel
      eqDeg
      (mapCtx (\ty -> Pair3 ty ty) gamma)
      (Pair3
        (_segment'content segment)
        ty
      )
    )
    (Just parent)
    "Checking whether actual type equals expected type."
checkEliminator parent gamma dmu eliminee tyEliminee Unbox ty = unreachable
-- dependent elims: type-check motive and take them separately
checkEliminator parent gamma dmu eliminee tyEliminee (ElimDep motive clauses) ty = do
  addNewConstraint
    (JudType
      (gamma :.. VarFromCtx <$> Declaration
        (DeclNameSegment $ _namedBinding'name motive)
        dmu
        Explicit
        (Type $ Expr3 $ TermCons $ ConsUniHS tyEliminee)
      )
      (_namedBinding'body motive)
    )
    (Just parent)
    "Type-checking motive."
  let subst :: VarExt _ -> Term _ _ _
      subst VarLast = eliminee
      subst (VarWkn v) = Var3 v
  addNewConstraint
    (JudTypeRel
      eqDeg
      (mapCtx (\ty -> Pair3 ty ty) gamma)
      (Pair3
        (swallow $ subst <$> _namedBinding'body motive)
        ty
      )
    )
    (Just parent)
    "Checking whether actual type equals expected type."
  checkDependentEliminator parent gamma dmu eliminee tyEliminee motive clauses ty

-------
    
checkTermNV :: forall mode modty rel tc v .
    (MonadTC mode modty rel tc, DeBruijnLevel v) =>
    Constraint mode modty rel ->
    Ctx Type mode modty v Void ->
    TermNV mode modty v ->
    Type mode modty v ->
    tc ()
checkTermNV parent gamma (TermCons c) ty = checkConstructorTerm parent gamma c ty
checkTermNV parent gamma (TermElim dmu eliminee tyEliminee eliminator) ty = do
  -- CMODE CMODTY
  addNewConstraint
    (JudType ((VarFromCtx <$> dmu) :\\ gamma) (Type $ Expr3 $ TermCons $ ConsUniHS $ tyEliminee))
    (Just parent)
    "Checking type of eliminee."
  addNewConstraint
    (JudTerm ((VarFromCtx <$> dmu) :\\ gamma) eliminee (Type $ Expr3 $ TermCons $ ConsUniHS $ tyEliminee))
    (Just parent)
    "Type-checking eliminee."
  checkEliminator parent gamma dmu eliminee tyEliminee eliminator ty
checkTermNV parent gamma t@(TermMeta meta (Compose depcies)) ty = do
  maybeT <- awaitMeta parent "I want to know what I'm supposed to type-check." meta depcies
  t' <- case maybeT of
    Nothing -> do
      -- Ideally, terms are type-checked only once. Hence, the first encounter is the best
      -- place to request eta-expansion.
      addNewConstraint
        (JudEta gamma (Expr3 t) ty)
        (Just parent)
        "Eta-expand meta if possible."
      -- The meta may now have a solution.
      maybeT' <- awaitMeta parent
                   "I want to know what I'm supposed to type-check. (Retry after trying to eta-expand)" meta depcies
      case maybeT' of
        Nothing -> tcBlock parent "I want to know what I'm supposed to type-check."
        Just t' -> return t'
    Just t' -> return t'
  childConstraint <- defConstraint
            (JudTerm gamma t' ty)
            (Just parent)
            "Look up meta."
  checkTerm childConstraint gamma t' ty
checkTermNV parent gamma (TermQName qname lookupresult) (Type ty) = do
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
checkTermNV parent gamma (TermSmartElim eliminee (Compose eliminators) result) ty = do
  dmuElim <- newMetaModedModality (Just parent) (irrModedModality :\\ gamma) "Infer modality of smart elimination."
  tyEliminee <- newMetaType (Just parent) eqDeg (VarFromCtx <$> dmuElim :\\ gamma) "Infer type of eliminee."
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
    (JudSmartElim gamma dmuElim eliminee tyEliminee eliminators result ty)
    (Just parent)
    "Smart elimination should reduce to its result."
checkTermNV parent gamma (TermGoal goalname result) ty = do
  -----
  addNewConstraint
    (JudTerm gamma result ty)
    (Just parent)
    "Goal should take value of the appropriate type."
  -----
  goalConstraint <- defConstraint
      (JudGoal gamma goalname result ty)
      (Just parent)
      "Goal should take some value."
  tcReport goalConstraint "This isn't my job; delegating to a human."
checkTermNV parent gamma (TermProblem t) (Type ty) = tcFail parent $ "Erroneous term."
checkTermNV parent gamma TermWildcard ty = unreachable

-------

checkTerm ::
    (MonadTC mode modty rel tc, DeBruijnLevel v) =>
    Constraint mode modty rel ->
    Ctx Type mode modty v Void ->
    Term mode modty v ->
    Type mode modty v ->
    tc ()
checkTerm parent gamma (Var3 v) (Type ty) = do
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
checkTerm parent gamma (Expr3 t) ty = checkTermNV parent gamma t ty
