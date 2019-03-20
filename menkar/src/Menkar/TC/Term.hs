module Menkar.TC.Term where

import Menkar.System.Fine
import Menkar.System.TC
import Menkar.Fine.Syntax
import Menkar.Basic.Context
import Menkar.Fine.Context
import Menkar.Fine.Judgement
import Menkar.Fine.LookupQName
import Menkar.TC.Segment
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
  {-lvl <- newMetaTerm
           (Just parent)
           topDeg
           (ModedModality dataMode irrMod :\\ gamma)
           (Type $ Expr2 $ TermCons $ ConsUniHS $ NatType)
           "Infer level."-}
  let currentUni = hs2type $ UniHS (unVarFromCtx <$> ctx'mode gamma) --lvl
  ----------
  checkSegmentUni parent gamma $ binding'segment binding
  ----------
  addNewConstraint
    (JudTerm
      (gamma :.. (VarFromCtx <$> binding'segment binding))
      (binding'body binding)
      (VarWkn <$> currentUni)
    )
    (Just parent)
    "Checking the codomain."
  ---------
  addNewConstraint
    (JudTypeRel
      (eqDeg :: Degree sys _)
      (mapCtx (\ty -> Twice2 ty ty) gamma)
      (Twice2 currentUni ty)
    )
    (Just parent)
    "Checking whether actual type equals expected type."

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
  let dgamma = unVarFromCtx <$> ctx'mode gamma
  addNewConstraint
    (JudModeRel (crispModedModality :\\ duplicateCtx gamma) d dgamma)
    (Just parent)
    "Checking whether actual mode equals expected mode."
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
  ----------
  checkSegmentUni parent gamma seg
  ---------
  addNewConstraint
    (JudTypeRel
      (eqDeg :: Degree sys _)
      (duplicateCtx gamma)
      (Twice2 currentUni ty)
    )
    (Just parent)
    "Checking whether actual type equals expected type."
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

checkConstructorTerm :: forall sys tc v .
    (SysTC sys, MonadTC sys tc, DeBruijnLevel v) =>
    Constraint sys ->
    Ctx Type sys v Void ->
    ConstructorTerm sys v ->
    Type sys v ->
    tc ()
checkConstructorTerm parent gamma (ConsUniHS t) ty = checkUniHSConstructor parent gamma t ty
checkConstructorTerm parent gamma (Lam binding) ty = do
  checkSegment parent gamma $ binding'segment binding
  ----------
  let dgamma = unVarFromCtx <$> ctx'mode gamma
  let dmu = _segment'modty $ binding'segment $ binding
  ----------
  codomain <- newMetaType
                (Just parent)
                --(eqDeg :: Degree sys _)
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
      (duplicateCtx gamma)
      (Twice2
        (hs2type $ Pi $ Binding (binding'segment binding) $ unType codomain)
        ty
      )
    )
    (Just parent)
    "Checking whether actual type equals expected type."
checkConstructorTerm parent gamma (Pair sigmaBinding t1 t2) ty = do
  let dmuSigma = _segment'modty $ binding'segment $ sigmaBinding
  let sigmaType = hs2type $ Sigma sigmaBinding
  ----------
  addNewConstraint
    (JudType gamma sigmaType)
    (Just parent)
    "Checking the type"
  ----------
  addNewConstraint
    (JudTerm
      (VarFromCtx <$> dmuSigma :\\ gamma)
      t1
      (_segment'content $ binding'segment $ sigmaBinding)
    )
    (Just parent)
    "Type-checking first component."
  ----------
  addNewConstraint
    (JudTerm gamma t2 (Type $ substLast2 t1 $ binding'body sigmaBinding))
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
  addNewConstraint
    (JudTypeRel
      (eqDeg :: Degree sys _)
      (mapCtx (\ty -> Twice2 ty ty) gamma)
      (Twice2 (Type $ Expr2 $ TermCons $ ConsUniHS $ UnitType) ty)
    )
    (Just parent)
    "Checking whether actual type equals expected type."
checkConstructorTerm parent gamma (ConsBox boxSeg t) ty = do
  let dmuBox = _segment'modty $ boxSeg
  let boxType = hs2type $ BoxType boxSeg
  ----------
  addNewConstraint
    (JudType gamma boxType)
    (Just parent)
    "Checking the type"
  ----------
  addNewConstraint
    (JudTerm
      (VarFromCtx <$> dmuBox :\\ gamma)
      t
      (_segment'content $ boxSeg)
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
  addNewConstraint
    (JudTypeRel
      (eqDeg :: Degree sys _)
      (mapCtx (\ty -> Twice2 ty ty) gamma)
      (Twice2 (Type $ Expr2 $ TermCons $ ConsUniHS $ NatType) ty)
    )
    (Just parent)
    "Checking whether actual type equals expected type."
checkConstructorTerm parent gamma (ConsSuc t) ty = do
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
  tyAmbient <- newMetaType (Just parent) {-(eqDeg :: Degree sys _)-} gamma "Inferring ambient type."
  t <- newMetaTerm (Just parent) {-(eqDeg :: Degree sys _)-} gamma tyAmbient MetaBlocked "Inferring self-equand."
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
  let zero :: Term sys _ = Expr2 $ TermCons $ ConsZero
  addNewConstraint
    (JudTerm gamma cz (substLast2 zero $ _namedBinding'body motive))
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
  let dmuPi = _segment'modty $ binding'segment $ binding
  let dom = _segment'content $ binding'segment binding
  addNewConstraint
    (JudTerm ((VarFromCtx <$> dmuPi) :\\ gamma) arg dom)
    (Just parent)
    "Type-checking argument."
  addNewConstraint
    (JudTypeRel
      (eqDeg :: Degree sys _)
      (mapCtx (\ty -> Twice2 ty ty) gamma)
      (Twice2
        (Type $ substLast2 arg $ binding'body binding)
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
      tmFst = Expr2 $ TermElim (ModedModality dSnd muProj) eliminee tyEliminee Fst
  addNewConstraint
    (JudTypeRel
      (eqDeg :: Degree sys _)
      (mapCtx (\ty -> Twice2 ty ty) gamma)
      (Twice2
        (Type $ substLast2 tmFst $ binding'body binding)
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
  addNewConstraint
    (JudTypeRel
      (eqDeg :: Degree sys _)
      (mapCtx (\ty -> Twice2 ty ty) gamma)
      (Twice2
        (substLast2 eliminee $ _namedBinding'body motive)
        ty
      )
    )
    (Just parent)
    "Checking whether actual type equals expected type."
  checkDependentEliminator parent gamma dmu eliminee tyEliminee motive clauses ty
checkEliminator parent gamma dmu eliminee (EqType tyAmbient tL tR) (ElimEq motive crefl) ty = do
  let dgamma = unVarFromCtx <$> ctx'mode gamma
  let bodyMotive = _namedBinding'body $ _namedBinding'body motive
  let segR = Declaration (DeclNameSegment $ _namedBinding'name motive) dmu Explicit tyAmbient
  let segEq = Declaration
               (DeclNameSegment $ _namedBinding'name $ _namedBinding'body $ motive)
               (idModedModality $ VarWkn <$> dgamma)
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
  let dgamma = unVarFromCtx <$> ctx'mode gamma
  addNewConstraint
    (JudModedModality (crispModedModality :\\ gamma) dmu dgamma)
    (Just parent)
    "Checking modality."
  addNewConstraint
    (JudType ((VarFromCtx <$> dmu) :\\ gamma) (hs2type $ tyEliminee))
    (Just parent)
    "Checking type of eliminee."
  addNewConstraint
    (JudTerm ((VarFromCtx <$> dmu) :\\ gamma) eliminee (hs2type $ tyEliminee))
    (Just parent)
    "Type-checking eliminee."
  checkEliminator parent gamma dmu eliminee tyEliminee eliminator ty
checkTermNV parent gamma t@(TermMeta neutrality meta (Compose depcies) alg) ty = do
  maybeT <- awaitMeta parent "I want to know what I'm supposed to type-check." meta depcies
  t' <- case maybeT of
    Nothing -> do
      {-
      -- Ideally, terms are type-checked only once. Hence, the first encounter is the best
      -- place to request eta-expansion.
      case neutrality of
        MetaBlocked -> addNewConstraint
          (JudEta gamma (Expr2 t) ty)
          (Just parent)
          "Eta-expand meta if possible."
        MetaNeutral -> return ()
      -}
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
  let ldivModAppliedVal = (leftDivided'content .~ telescoped2modalQuantified d2 telescope) lookupresult
  addNewConstraint
    (JudModedModalityRel ModLeq
      (duplicateCtx gamma)
      (_modApplied'modality . _leftDivided'content $ ldivModAppliedVal)
      (_leftDivided'modality $ ldivModAppliedVal)
      (_leftDivided'originalMode $ ldivModAppliedVal)
    )
    (Just parent)
    "Checking that variable is accessible."
  addNewConstraint
    (JudTypeRel
      (eqDeg :: Degree sys _)
      (mapCtx (\ty -> Twice2 ty ty) gamma)
      (Twice2
        (_val'type . _modApplied'content . _leftDivided'content $ ldivModAppliedVal)
        (Type ty)
      )
    )
    (Just parent)
    "Checking whether actual type equals expected type."
checkTermNV parent gamma (TermAlgorithm (AlgSmartElim eliminee (Compose eliminators)) result) ty = do
  let dgamma = unVarFromCtx <$> ctx'mode gamma
  let dmuElim = concatModedModalityDiagrammatically (fst2 <$> eliminators) dgamma
  tyEliminee <- newMetaType (Just parent) {-(eqDeg :: Degree sys _)-}
                  (VarFromCtx <$> dmuElim :\\ gamma) "Infer type of eliminee."
  -----
  addNewConstraint
    (JudTerm (VarFromCtx <$> dmuElim :\\ gamma) eliminee tyEliminee)
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
  let ldivSeg = unVarFromCtx <$> lookupVar gamma v
  addNewConstraint
    (JudModedModalityRel ModLeq
      (duplicateCtx gamma)
      (_decl'modty . _leftDivided'content $ ldivSeg)
      (_leftDivided'modality $ ldivSeg)
      (_leftDivided'originalMode $ ldivSeg)
    )
    (Just parent)
    "Checking that variable is accessible."
  addNewConstraint
    (JudTypeRel
      (eqDeg :: Degree sys _)
      (mapCtx (\ty -> Twice2 ty ty) gamma)
      (Twice2
        (_decl'content . _leftDivided'content $ ldivSeg)
        (Type ty)
      )
    )
    (Just parent)
    "Checking whether actual type equals expected type."
checkTerm parent gamma (Expr2 t) ty = checkTermNV parent gamma t ty
