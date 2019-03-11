module Menkar.TC.Term where

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

import Data.Void
import Control.Lens
import Data.Functor.Compose
import Control.Monad

-- CMODE means you need to check a mode
-- CMODTY means you need to check a modality

checkPiOrSigma :: forall sys tc v .
    (SysTC sys, MonadTC sys tc, DeBruijnLevel v) =>
    Constraint sys ->
    Ctx Type sys v Void ->
    Binding Type Term sys v ->
    Type sys v ->
    tc ()
checkPiOrSigma parent gamma binding ty = do
  -- CMODE
  -- CMODTY
  {-lvl <- newMetaTerm
           (Just parent)
           topDeg
           (ModedModality dataMode irrMod :\\ gamma)
           (Type $ Expr2 $ TermCons $ ConsUniHS $ NatType)
           "Infer level."-}
  let currentUni = hs2type $ UniHS (unVarFromCtx <$> ctx'mode gamma) --lvl
  ---------
  addNewConstraint
    (JudTypeRel
      (eqDeg :: Degree sys _)
      (mapCtx (\ty -> Twice2 ty ty) gamma)
      (Twice2 currentUni ty)
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
    "Checking the domain."
  ----------
  addNewConstraint
    (JudTerm
      (gamma :.. (VarFromCtx <$> binding'segment binding))
      (binding'body binding)
      (VarWkn <$> currentUni)
    )
    (Just parent)
    "Checking the codomain."

-------

checkUni :: forall sys tc v .
    (SysTC sys, MonadTC sys tc, DeBruijnLevel v) =>
    Constraint sys ->
    Ctx Type sys v Void ->
    Type sys v ->
    tc ()
checkUni parent gamma ty = do
  {-lvl <- newMetaTerm
           (Just parent)
           topDeg
           (ModedModality dataMode irrMod :\\ gamma)
           (Type $ Expr2 $ TermCons $ ConsUniHS $ NatType)
           "Infer level."-}
  let currentUni = hs2type $ UniHS (unVarFromCtx <$> ctx'mode gamma) --lvl
  ---------
  addNewConstraint
    (JudTypeRel
      (eqDeg :: Degree sys _)
      (duplicateCtx gamma)
      (Twice2 currentUni ty)
    )
    (Just parent)
    "Checking whether actual type equals expected type."

-------

checkUniHSConstructor :: forall sys tc v .
    (SysTC sys, MonadTC sys tc, DeBruijnLevel v) =>
    Constraint sys ->
    Ctx Type sys v Void ->
    UniHSConstructor sys v ->
    Type sys v ->
    tc ()
checkUniHSConstructor parent gamma (UniHS d {-lvl-}) ty = do
  -- CMODE d
  -----
  {-addNewConstraint
    (JudTerm
      (ModedModality dataMode irrMod :\\ gamma)
      lvl
      (Type $ Expr2 $ TermCons $ ConsUniHS $ NatType)
    )
    (Just parent)
    "Checking the level."-}
  -----
  {-anyLvl <- newMetaTerm
           (Just parent)
           topDeg
           (ModedModality dataMode irrMod :\\ gamma)
           (Type $ Expr2 $ TermCons $ ConsUniHS $ NatType)
           ("Inferring some level. The level of the universe we're checking, " ++
           "plus this level, plus 1 is the level of the containing universe.")
  let biggerLvl =
        -- biggerLvl = suc (lvl + anyLvl)
        Expr2 . TermCons . ConsSuc $
        Expr2 $ TermElim (idModedModality dataMode) lvl NatType $
        ElimDep (NamedBinding Nothing $ Type $ Expr2 $ TermCons $ ConsUniHS $ NatType) $
        ElimNat
          anyLvl
          (NamedBinding Nothing $ NamedBinding (Just $ Raw.Name Raw.NonOp "l")$ Expr2 . TermCons . ConsSuc $ Var2 VarLast)-}
  checkUni parent gamma ty
checkUniHSConstructor parent gamma (Pi binding) ty = checkPiOrSigma parent gamma binding ty
checkUniHSConstructor parent gamma (Sigma binding) ty = checkPiOrSigma parent gamma binding ty
checkUniHSConstructor parent gamma (EmptyType) ty = checkUni parent gamma ty
checkUniHSConstructor parent gamma (UnitType) ty = checkUni parent gamma ty
checkUniHSConstructor parent gamma (BoxType seg) ty = do
  {-lvl <- newMetaTerm
           (Just parent)
           topDeg
           (ModedModality dataMode irrMod :\\ gamma)
           (Type $ Expr2 $ TermCons $ ConsUniHS $ NatType)
           "Infer level."-}
  let currentUni = Type $ Expr2 $ TermCons $ ConsUniHS $ UniHS (unVarFromCtx <$> ctx'mode gamma) --lvl
  ---------
  addNewConstraint
    (JudTypeRel
      (eqDeg :: Degree sys _)
      (duplicateCtx gamma)
      (Twice2 currentUni ty)
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
checkUniHSConstructor parent gamma (EqType tyAmbient tyL tyR) ty = do
  checkUni parent gamma ty
  addNewConstraint
    (JudType gamma tyAmbient)
    (Just parent)
    "Checking ambient type."
  addNewConstraint
    (JudTerm gamma tyL tyAmbient)
    (Just parent)
    "Checking left equand."
  addNewConstraint
    (JudTerm gamma tyR tyAmbient)
    (Just parent)
    "Checking right equand."
--checkUniHSConstructor parent gamma t ty = _checkUniHSConstructor
-- CMODE do we allow Empty, Unit and Nat in arbitrary mode? I guess not...

checkConstructorTerm :: forall sys tc v .
    (SysTC sys, MonadTC sys tc, DeBruijnLevel v) =>
    Constraint sys ->
    Ctx Type sys v Void ->
    ConstructorTerm sys v ->
    Type sys v ->
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
                (eqDeg :: Degree sys _)
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
      (eqDeg :: Degree sys _)
      (mapCtx (\ty -> Twice2 ty ty) gamma)
      (Twice2
        (Type $ Expr2 $ TermCons $ ConsUniHS $ Pi $ Binding (binding'segment binding) $ unType codomain)
        ty
      )
    )
    (Just parent)
    "Checking whether actual type equals expected type."
checkConstructorTerm parent gamma (Pair sigmaBinding t1 t2) ty = do
  let sigmaType = Type $ Expr2 $ TermCons $ ConsUniHS $ Sigma sigmaBinding
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
  let subst :: VarExt _ -> Term _ _
      subst VarLast = t1
      subst (VarWkn v) = Var2 v
  addNewConstraint
    (JudTerm gamma t2 (Type $ join $ subst <$> binding'body sigmaBinding))
    (Just parent)
    "Type-checking second component."
  ----------
  addNewConstraint
    (JudTypeRel
      (eqDeg :: Degree sys _)
      (mapCtx (\ty -> Twice2 ty ty) gamma)
      (Twice2 sigmaType ty)
    )
    (Just parent)
    "Checking whether actual type equals expected type."
checkConstructorTerm parent gamma ConsUnit ty = do
  -- CMODE
  ----------
  addNewConstraint
    (JudTypeRel
      (eqDeg :: Degree sys _)
      (mapCtx (\ty -> Twice2 ty ty) gamma)
      (Twice2 (Type $ Expr2 $ TermCons $ ConsUniHS $ UnitType) ty)
    )
    (Just parent)
    "Checking whether actual type equals expected type."
checkConstructorTerm parent gamma (ConsBox typeSegment t) ty = do
  let boxType = Type $ Expr2 $ TermCons $ ConsUniHS $ BoxType typeSegment
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
      (eqDeg :: Degree sys _)
      (mapCtx (\ty -> Twice2 ty ty) gamma)
      (Twice2 boxType ty)
    )
    (Just parent)
    "Checking whether actual type equals expected type."
checkConstructorTerm parent gamma ConsZero ty = do
  -- CMODE
  ----------
  addNewConstraint
    (JudTypeRel
      (eqDeg :: Degree sys _)
      (mapCtx (\ty -> Twice2 ty ty) gamma)
      (Twice2 (Type $ Expr2 $ TermCons $ ConsUniHS $ NatType) ty)
    )
    (Just parent)
    "Checking whether actual type equals expected type."
checkConstructorTerm parent gamma (ConsSuc t) ty = do
  -- CMODE
  ----------
  addNewConstraint
    (JudTerm gamma t (Type $ Expr2 $ TermCons $ ConsUniHS $ NatType))
    (Just parent)
    "Type-checking predecessor."
  ----------
  addNewConstraint
    (JudTypeRel
      (eqDeg :: Degree sys _)
      (duplicateCtx gamma)
      (Twice2 (Type $ Expr2 $ TermCons $ ConsUniHS $ NatType) ty)
    )
    (Just parent)
    "Checking whether actual type equals expected type."
checkConstructorTerm parent gamma ConsRefl ty = do
  tyAmbient <- newMetaType (Just parent) (eqDeg :: Degree sys _) gamma "Inferring ambient type."
  t <- newMetaTerm (Just parent) (eqDeg :: Degree sys _) gamma tyAmbient True "Inferring self-equand."
  addNewConstraint
    (JudTypeRel
      (eqDeg :: Degree sys _)
      (duplicateCtx gamma)
      (Twice2 (hs2type $ EqType tyAmbient t t) ty)
    )
    (Just parent)
    "Checking whether actual type equals expected type."
--checkConstructorTerm parent gamma c (Type ty) = _checkConstructorTerm

-------

checkDependentEliminator :: forall sys tc v .
    (SysTC sys, MonadTC sys tc, DeBruijnLevel v) =>
    Constraint sys ->
    Ctx Type sys v Void ->
    ModedModality sys v ->
    Term sys v ->
    UniHSConstructor sys v ->
    NamedBinding Type sys v ->
    DependentEliminator sys v ->
    Type sys v ->
    tc ()
checkDependentEliminator parent gamma dmu eliminee
    tyEliminee@(Sigma sigmaBinding) motive (ElimSigma clause) ty = do
  let segFst :: Segment Type _ _
      segFst = Declaration
                 (DeclNameSegment $ _namedBinding'name clause)
                 (compModedModality dmu (_segment'modty $ binding'segment $ sigmaBinding))
                 Explicit
                 (_segment'content $ binding'segment $ sigmaBinding)
  let segSnd :: Segment Type _ (VarExt _)
      segSnd = Declaration
                 (DeclNameSegment $ _namedBinding'name $ _namedBinding'body clause)
                 (VarWkn <$> dmu)
                 Explicit
                 (Type $ binding'body sigmaBinding)
  let subst :: VarExt _ -> Term _ (VarExt (VarExt _))
      subst VarLast = Expr2 $ TermCons $ Pair (VarWkn . VarWkn <$> sigmaBinding) (Var2 $ VarWkn VarLast) (Var2 VarLast)
      subst (VarWkn v) = Var2 $ VarWkn $ VarWkn v
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
  let segContent :: Segment Type _ _
      segContent = Declaration
                     (DeclNameSegment $ _namedBinding'name clause)
                     (compModedModality dmu (_segment'modty boxSeg))
                     Explicit
                     (_segment'content boxSeg)
  let subst :: VarExt _ -> Term _ (VarExt _)
      subst VarLast = Expr2 $ TermCons $ ConsBox (VarWkn <$> boxSeg) $ Var2 VarLast
      subst (VarWkn v) = Var2 $ VarWkn v
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
  let substZ :: VarExt v -> Term sys v
      substZ VarLast = Expr2 $ TermCons $ ConsZero
      substZ (VarWkn v) = Var2 v
  addNewConstraint
    (JudTerm gamma cz (swallow $ substZ <$> _namedBinding'body motive))
    (Just parent)
    "Type-checking zero clause."
  let segPred :: Segment Type _ _
      segPred = Declaration
                  (DeclNameSegment $ _namedBinding'name cs)
                  dmu
                  Explicit
                  (Type $ Expr2 $ TermCons $ ConsUniHS $ NatType)
  let segHyp :: Segment Type _ (VarExt _)
      segHyp = Declaration
                  (DeclNameSegment $ _namedBinding'name $ _namedBinding'body cs)
                  (idModedModality $ VarWkn . unVarFromCtx <$> ctx'mode gamma)
                  Explicit
                  (_namedBinding'body motive)
  let substS :: VarExt v -> Term sys (VarExt (VarExt v))
      substS VarLast = Expr2 $ TermCons $ ConsSuc $ Var2 $ VarWkn VarLast
      substS (VarWkn v) = Var2 $ VarWkn $ VarWkn v
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

{-| Checks whether the eliminator applies and has the correct output type. -}
checkEliminator :: forall sys tc v .
    (SysTC sys, MonadTC sys tc, DeBruijnLevel v) =>
    Constraint sys ->
    Ctx Type sys v Void ->
    ModedModality sys v ->
    Term sys v ->
    UniHSConstructor sys v ->
    Eliminator sys v ->
    Type sys v ->
    tc ()
checkEliminator parent gamma dmu eliminee (Pi binding) (App arg) ty = do
  let dmu = _segment'modty $ binding'segment $ binding
  let dom = _segment'content $ binding'segment binding
  addNewConstraint
    (JudTerm ((VarFromCtx <$> dmu) :\\ gamma) arg dom)
    (Just parent)
    "Type-checking argument."
  let subst :: VarExt _ -> Term _ _
      subst VarLast = arg
      subst (VarWkn v) = Var2 v
  addNewConstraint
    (JudTypeRel
      (eqDeg :: Degree sys _)
      (mapCtx (\ty -> Twice2 ty ty) gamma)
      (Twice2
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
      (eqDeg :: Degree sys _)
      (mapCtx (\ty -> Twice2 ty ty) gamma)
      (Twice2
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
      subst :: VarExt _ -> Term _ _
      subst VarLast = Expr2 $ TermElim (ModedModality dSnd muProj) eliminee tyEliminee Fst
      subst (VarWkn v) = Var2 v
  addNewConstraint
    (JudTypeRel
      (eqDeg :: Degree sys _)
      (mapCtx (\ty -> Twice2 ty ty) gamma)
      (Twice2
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
      (eqDeg :: Degree sys _)
      (mapCtx (\ty -> Twice2 ty ty) gamma)
      (Twice2
        (_segment'content segment)
        ty
      )
    )
    (Just parent)
    "Checking whether actual type equals expected type."
checkEliminator parent gamma dmu eliminee tyEliminee Unbox ty = unreachable
checkEliminator parent gamma dmu eliminee
    tyEliminee@(Pi (Binding seg (Expr2 (TermCons (ConsUniHS (EqType tyAmbient tL tR)))))) Funext ty = do
  let tyPiAmbient = hs2type $ Pi $ Binding seg $ unType tyAmbient
  let tLamL = Expr2 $ TermCons $ Lam $ Binding seg $ tL
  let tLamR = Expr2 $ TermCons $ Lam $ Binding seg $ tR
  addNewConstraint
    (JudTypeRel
      (eqDeg :: Degree sys _)
      (duplicateCtx gamma)
      (Twice2
        (hs2type $ EqType tyPiAmbient tLamL tLamR)
        ty
      )
    )
    (Just parent)
    "Checking whether actual type equals expected type."
checkEliminator parent gamma dmu eliminee tyEliminee Funext ty = unreachable
-- dependent elims: type-check motive and take them separately
checkEliminator parent gamma dmu eliminee tyEliminee (ElimDep motive clauses) ty = do
  addNewConstraint
    (JudType
      (gamma :.. VarFromCtx <$> Declaration
        (DeclNameSegment $ _namedBinding'name motive)
        dmu
        Explicit
        (Type $ Expr2 $ TermCons $ ConsUniHS tyEliminee)
      )
      (_namedBinding'body motive)
    )
    (Just parent)
    "Type-checking motive."
  let subst :: VarExt _ -> Term _ _
      subst VarLast = eliminee
      subst (VarWkn v) = Var2 v
  addNewConstraint
    (JudTypeRel
      (eqDeg :: Degree sys _)
      (mapCtx (\ty -> Twice2 ty ty) gamma)
      (Twice2
        (swallow $ subst <$> _namedBinding'body motive)
        ty
      )
    )
    (Just parent)
    "Checking whether actual type equals expected type."
  checkDependentEliminator parent gamma dmu eliminee tyEliminee motive clauses ty
checkEliminator parent gamma dmu eliminee (EqType tyAmbient tL tR) (ElimEq motive crefl) ty = do
  let bodyMotive = _namedBinding'body $ _namedBinding'body motive
  let segR = Declaration (DeclNameSegment $ _namedBinding'name motive) dmu Explicit tyAmbient
  let segEq = Declaration
               (DeclNameSegment $ _namedBinding'name $ _namedBinding'body $ motive)
               (VarWkn <$> dmu)
               Explicit
               (hs2type $ EqType (VarWkn <$> tyAmbient) (VarWkn <$> tL) (Var2 VarLast))
  addNewConstraint
    (JudType
      (gamma :.. VarFromCtx <$> segR :.. VarFromCtx <$> segEq)
      (_namedBinding'body $ _namedBinding'body motive)
    )
    (Just parent)
    "Checking the motive"
  addNewConstraint
    (JudTerm gamma crefl (substLast2 tL $ substLast2 (Expr2 $ TermCons $ ConsRefl :: Term sys _) $ bodyMotive))
    (Just parent)
    "Type-checking refl-clause."
  addNewConstraint
    (JudTypeRel
      (eqDeg :: Degree sys _)
      (duplicateCtx gamma)
      (Twice2 (substLast2 tR $ substLast2 (VarWkn <$> eliminee) $ bodyMotive) ty)
    )
    (Just parent)
    "Checking whether actual type equals expected type."
checkEliminator parent gamma dmu eliminee tyEliminee (ElimEq motive crefl) ty = unreachable

-------
    
checkTermNV :: forall sys tc v .
    (SysTC sys, MonadTC sys tc, DeBruijnLevel v) =>
    Constraint sys ->
    Ctx Type sys v Void ->
    TermNV sys v ->
    Type sys v ->
    tc ()
checkTermNV parent gamma (TermCons c) ty = checkConstructorTerm parent gamma c ty
checkTermNV parent gamma (TermElim dmu eliminee tyEliminee eliminator) ty = do
  -- CMODE CMODTY
  addNewConstraint
    (JudType ((VarFromCtx <$> dmu) :\\ gamma) (Type $ Expr2 $ TermCons $ ConsUniHS $ tyEliminee))
    (Just parent)
    "Checking type of eliminee."
  addNewConstraint
    (JudTerm ((VarFromCtx <$> dmu) :\\ gamma) eliminee (Type $ Expr2 $ TermCons $ ConsUniHS $ tyEliminee))
    (Just parent)
    "Type-checking eliminee."
  checkEliminator parent gamma dmu eliminee tyEliminee eliminator ty
checkTermNV parent gamma t@(TermMeta etaFlag meta (Compose depcies) alg) ty = do
  maybeT <- awaitMeta parent "I want to know what I'm supposed to type-check." meta depcies
  t' <- case maybeT of
    Nothing -> do
      -- Ideally, terms are type-checked only once. Hence, the first encounter is the best
      -- place to request eta-expansion.
      when etaFlag $ addNewConstraint
        (JudEta gamma (Expr2 t) ty)
        (Just parent)
        "Eta-expand meta if possible."
      tcBlock parent "I want to know what I'm supposed to type-check."
      {-
      -- The meta may now have a solution.
      maybeT' <- awaitMeta parent
                   "I want to know what I'm supposed to type-check. (Retry after trying to eta-expand)" meta depcies
      case maybeT' of
        Nothing -> tcBlock parent "I want to know what I'm supposed to type-check."
        Just t' -> return t'
      -}
    Just t' -> return t'
  childConstraint <- defConstraint
            (JudTerm gamma t' ty)
            (Just parent)
            "Look up meta."
  checkTerm childConstraint gamma t' ty
checkTermNV parent gamma (TermQName qname lookupresult) (Type ty) = do
  let (LeftDivided d2 d1mu telescope) = lookupresult
  let ldivModAppliedVal = VarFromCtx <$> (leftDivided'content .~ telescoped2modalQuantified d2 telescope) lookupresult
  varAccessible <- leqMod
        (modality'mod . _modApplied'modality . _leftDivided'content $ ldivModAppliedVal)
        (modality'mod . _leftDivided'modality $ ldivModAppliedVal)
  if varAccessible
        then do
          addNewConstraint
            (JudTypeRel
              (eqDeg :: Degree sys _)
              (mapCtx (\ty -> Twice2 ty ty) gamma)
              (Twice2
                (unVarFromCtx <$> (_val'type . _modApplied'content . _leftDivided'content $ ldivModAppliedVal))
                (Type ty)
              )
            )
            (Just parent)
            "Checking whether actual type equals expected type."
        else tcFail parent $ "Object cannot be used here: modality restrictions are too strong."
checkTermNV parent gamma (TermAlgorithm (AlgSmartElim eliminee (Compose eliminators)) result) ty = do
  dmuElim <- newMetaModedModality (Just parent) (flatModedModality :\\ gamma) "Infer modality of smart elimination."
  tyEliminee <- newMetaType (Just parent) (eqDeg :: Degree sys _) (VarFromCtx <$> dmuElim :\\ gamma) "Infer type of eliminee."
  -----
  -- CMODE
  addNewConstraint
    (JudTerm gamma eliminee tyEliminee)
    (Just parent)
    "Type-check the eliminee."
  -----
  addNewConstraint
    (JudTerm gamma result ty)
    (Just parent)
    "Type-check the result."
  -----
  addNewConstraint
    (JudSmartElim gamma {-dmuElim-} eliminee tyEliminee eliminators result ty)
    (Just parent)
    "Smart elimination should reduce to its result."
checkTermNV parent gamma (TermAlgorithm (AlgGoal goalname depcies) result) ty = do
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
checkTermNV parent gamma (TermSys t) ty = checkTermSys parent gamma t ty
checkTermNV parent gamma (TermProblem t) (Type ty) = tcFail parent $ "Erroneous term."
checkTermNV parent gamma TermWildcard ty = unreachable

-------

checkTerm :: forall sys tc v .
    (SysTC sys, MonadTC sys tc, DeBruijnLevel v) =>
    Constraint sys ->
    Ctx Type sys v Void ->
    Term sys v ->
    Type sys v ->
    tc ()
checkTerm parent gamma (Var2 v) (Type ty) = do
  let ldivSeg = lookupVar gamma v
  varAccessible <- leqMod
    (modality'mod . _decl'modty . _leftDivided'content $ ldivSeg)
    (modality'mod . _leftDivided'modality $ ldivSeg)
  if varAccessible
    then do
      addNewConstraint
        (JudTypeRel
          (eqDeg :: Degree sys _)
          (mapCtx (\ty -> Twice2 ty ty) gamma)
          (Twice2
            (unVarFromCtx <$> (_decl'content . _leftDivided'content $ ldivSeg))
            (Type ty)
          )
        )
        (Just parent)
        "Checking whether actual type equals expected type."
    else tcFail parent $ "Variable cannot be used here: modality restrictions are too strong."
checkTerm parent gamma (Expr2 t) ty = checkTermNV parent gamma t ty
