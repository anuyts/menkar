module Menkar.TC.Inference.Rel where

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

checkSegmentRel :: (MonadTC mode modty rel tc, Eq v) =>
  Constraint mode modty rel ->
  rel v ->
  Ctx (Pair3 Type) mode modty v Void ->
  Segment Type mode modty v ->
  Segment Type mode modty v ->
  tc ()
checkSegmentRel parent deg gamma seg1 seg2 = do
  -- CMOD check equality of modalities
  let d' = unVarFromCtx <$> ctx'mode gamma
  let uni = Type $ Expr3 $ TermCons $ ConsUniHS $ UniHS d' $ Expr3 TermWildcard
  addNewConstraint
    (JudTermRel
      deg
      gamma
      (Pair3
        (unType $ _segment'content seg1)
        (unType $ _segment'content seg2)
      )
      (Pair3 uni uni)
    )
    (Just parent)
    "Relating domains."      

checkPiOrSigmaRel :: (MonadTC mode modty rel tc, Eq v) =>
  Constraint mode modty rel ->
  rel v ->
  Ctx (Pair3 Type) mode modty v Void ->
  Binding Type Term mode modty v ->
  Binding Type Term mode modty v ->
  Type mode modty v ->
  Type mode modty v ->
  tc ()
checkPiOrSigmaRel parent deg gamma binding1 binding2 ty1 ty2 = do
    let seg1 = (binding'segment binding1)
    let seg2 = (binding'segment binding2)
    let dom2 = _segment'content $ binding'segment binding2
    let seg = over decl'content (\ dom1 -> Pair3 dom1 dom2) seg1
    let d' = unVarFromCtx <$> ctx'mode gamma
    let uni = Type $ Expr3 $ TermCons $ ConsUniHS $ UniHS (VarWkn <$> d') $ Expr3 TermWildcard
    checkSegmentRel parent deg gamma seg1 seg2
    addNewConstraint
      (JudTermRel
        (VarWkn <$> deg)
        (gamma :.. VarFromCtx <$> seg)
        (Pair3
          (binding'body binding1)
          (binding'body binding2)
        )
        (Pair3 uni uni)
      )
      (Just parent)
      "Relating codomains."

checkUniHSConstructorRel :: (MonadTC mode modty rel tc, Eq v) =>
  Constraint mode modty rel ->
  rel v ->
  Ctx (Pair3 Type) mode modty v Void ->
  UniHSConstructor mode modty v ->
  UniHSConstructor mode modty v ->
  Type mode modty v ->
  Type mode modty v ->
  tc ()
checkUniHSConstructorRel parent deg gamma t1 t2 ty1 ty2 = case (t1, t2) of
  (UniHS d1 lvl1, UniHS d2 lvl2) -> do
    let nat = Type $ Expr3 $ TermCons $ ConsUniHS $ NatType
    addNewConstraint
      (JudTermRel
        (divDeg irrModedModality deg)
        (irrModedModality :\\ gamma)
        (Pair3 lvl1 lvl2)
        (Pair3 nat nat)
      )
      (Just parent)
      "Relating levels."
  (UniHS _ _, _) -> tcFail parent "False."
  (Pi binding1, Pi binding2) -> checkPiOrSigmaRel parent deg gamma binding1 binding2 ty1 ty2
  (Pi _, _) -> tcFail parent "False."
  (Sigma binding1, Sigma binding2) -> checkPiOrSigmaRel parent deg gamma binding1 binding2 ty1 ty2
  (Sigma _, _) -> tcFail parent "False."
  (EmptyType, EmptyType) -> return ()
  (EmptyType, _) -> tcFail parent "False."
  (UnitType, UnitType) -> return ()
  (UnitType, _) -> tcFail parent "False."
  (BoxType seg1, BoxType seg2) -> checkSegmentRel parent deg gamma seg1 seg2
  (BoxType _, _) -> tcFail parent "False."
  (NatType, NatType) -> return ()
  (NatType, _) -> tcFail parent "False."
  --(_, _) -> _checkUniHSConstructorRel

--------------------------------

checkConstructorTermRel :: (MonadTC mode modty rel tc, Eq v) =>
  Constraint mode modty rel ->
  rel v ->
  Ctx (Pair3 Type) mode modty v Void ->
  ConstructorTerm mode modty v ->
  ConstructorTerm mode modty v ->
  Type mode modty v ->
  Type mode modty v ->
  tc ()
checkConstructorTermRel parent deg gamma t1 t2 ty1 ty2 = case (t1, t2) of
  (ConsUniHS c1, ConsUniHS c2) -> checkUniHSConstructorRel parent deg gamma c1 c2 ty1 ty2
  (ConsUniHS _, _) -> tcFail parent "False."
  -- Encountering a lambda is not possible: it's well-typed, so the type is a Pi-type, so eta-expansion has fired.
  (Lam binding, _) -> tcFail parent "LHS is presumed to be well-typed."
  (_, Lam binding) -> tcFail parent "RHS is presumed to be well-typed."
  (Pair sigmaBinding1 fst1 snd1, Pair sigmaBinding2 fst2 snd2) -> do
    let dmu = _segment'modty $ binding'segment $ sigmaBinding1
        dom1 = _segment'content $ binding'segment $ sigmaBinding1
        dom2 = _segment'content $ binding'segment $ sigmaBinding2
        cod1 = binding'body sigmaBinding1
        cod2 = binding'body sigmaBinding2
    addNewConstraint
      (JudTermRel
        (divDeg dmu deg)
        (VarFromCtx <$> dmu :\\ gamma)
        (Pair3 fst1 fst2)
        (Pair3 dom1 dom2)
      )
      (Just parent)
      "Relating first components."
    addNewConstraint
      (JudTermRel
        deg
        gamma
        (Pair3 snd1 snd2)
        (Pair3
          (Type $ substLast3 fst1 $ cod1)
          (Type $ substLast3 fst2 $ cod2)
        )
      )
      (Just parent)
      "Relating second components."
  (Pair _ _ _, _) -> tcFail parent "False."
  -- Encountering a unit is not possible: it's well-typed, so the type is a Pi-type, so eta-expansion has fired.
  (ConsUnit, _) -> tcFail parent "LHS is presumed to be well-typed."
  (_, ConsUnit) -> tcFail parent "RHS is presumed to be well-typed."
  (ConsBox boxSeg1 unbox1, ConsBox boxSeg2 unbox2) -> do
    let dmu = _segment'modty $ boxSeg1
        dom1 = _segment'content $ boxSeg1
        dom2 = _segment'content $ boxSeg2
    addNewConstraint
      (JudTermRel
        (divDeg dmu deg)
        (VarFromCtx <$> dmu :\\ gamma)
        (Pair3 unbox1 unbox2)
        (Pair3 dom1 dom2)
      )
      (Just parent)
      "Relating box contents."
  (ConsBox _ _, _) -> tcFail parent "False."
  (ConsZero, ConsZero) -> return ()
  (ConsZero, _) -> tcFail parent "False."
  (ConsSuc n1, ConsSuc n2) -> do
    let nat = Type $ Expr3 $ TermCons $ ConsUniHS $ NatType
    addNewConstraint
      (JudTermRel deg gamma (Pair3 n1 n2) (Pair3 nat nat))
      (Just parent)
      "Relating predecessors."
  (ConsSuc _, _) -> tcFail parent "False."
  --(_, _) -> _checkConstructorTermRel

checkDependentEliminatorRel :: (MonadTC mode modty rel tc, Eq v) =>
  Constraint mode modty rel ->
  rel v ->
  Ctx (Pair3 Type) mode modty v Void ->
  ModedModality mode modty v ->
  Term mode modty v ->
  Term mode modty v ->
  Type mode modty v ->
  Type mode modty v ->
  NamedBinding Term mode modty v ->
  NamedBinding Term mode modty v ->
  DependentEliminator mode modty v ->
  DependentEliminator mode modty v ->
  Type mode modty v ->
  Type mode modty v ->
  tc ()
checkDependentEliminatorRel parent deg gamma dmu
  eliminee1 eliminee2
  tyEliminee1 tyEliminee2
  motive1 motive2
  clauses1 clauses2
  ty1 ty2 = _checkDependentEliminatorRel

checkEliminatorRel :: (MonadTC mode modty rel tc, Eq v) =>
  Constraint mode modty rel ->
  rel v ->
  Ctx (Pair3 Type) mode modty v Void ->
  ModedModality mode modty v ->
  Term mode modty v ->
  Term mode modty v ->
  Type mode modty v ->
  Type mode modty v ->
  Eliminator mode modty v ->
  Eliminator mode modty v ->
  Type mode modty v ->
  Type mode modty v ->
  tc ()
checkEliminatorRel parent deg gamma dmu
  eliminee1 eliminee2
  tyEliminee1 tyEliminee2
  eliminator1 eliminator2
  ty1 ty2 = case (eliminator1, eliminator2) of
  (App arg1, App arg2) -> case (unType tyEliminee1, unType tyEliminee2) of
    (Expr3 (TermCons (ConsUniHS (Pi binding1))), Expr3 (TermCons (ConsUniHS (Pi binding2)))) -> do
      let dmu = _segment'modty $ binding'segment $ binding1
      let dom1 = _segment'content $ binding'segment binding1
      let dom2 = _segment'content $ binding'segment binding2
      addNewConstraint
        (JudTermRel
          (divDeg dmu deg)
          (VarFromCtx <$> dmu :\\ gamma)
          (Pair3 arg1 arg2)
          (Pair3 dom1 dom2)
        )
        (Just parent)
        "Relating arguments."
    (_, _) -> unreachable
  (App _, _) -> tcFail parent "False."
  (Fst, Fst) -> return ()
  (Fst, _) -> tcFail parent "False."
  (Snd, Snd) -> return ()
  (Snd, _) -> tcFail parent "False."
  (Unbox, Unbox) -> return ()
  (Unbox, _) -> tcFail parent "False."
  (ElimDep motive1 clauses1, ElimDep motive2 clauses2) -> do
    let seg = Declaration (DeclNameSegment $ _namedBinding'name motive1) dmu Explicit (Pair3 tyEliminee1 tyEliminee2)
    addNewConstraint
      (JudTypeRel
        (VarWkn <$> deg)
        (gamma :.. VarFromCtx <$> seg)
        (Pair3 (Type $ _namedBinding'body motive1) (Type $ _namedBinding'body motive2))
      )
      (Just parent)
      "Relating the motives."
    checkDependentEliminatorRel parent deg gamma dmu
      eliminee1 eliminee2
      tyEliminee1 tyEliminee2
      motive1 motive2
      clauses1 clauses2
      ty1 ty2
  (ElimDep _ _, _) -> tcFail parent "False."
  --(_, _) -> _checkEliminatorRel

checkTermNVRelNormal :: (MonadTC mode modty rel tc, Eq v) =>
  Constraint mode modty rel ->
  rel v ->
  Ctx (Pair3 Type) mode modty v Void ->
  TermNV mode modty v ->
  TermNV mode modty v ->
  Type mode modty v ->
  Type mode modty v ->
  tc ()
checkTermNVRelNormal parent deg gamma t1 t2 ty1 ty2 = case (t1, t2) of
  (TermCons c1, TermCons c2) -> checkConstructorTermRel parent deg gamma c1 c2 ty1 ty2
  (TermCons _, _) -> tcFail parent "False."
  (TermElim dmu1 eliminee1 tyEliminee1 eliminator1, TermElim dmu2 eliminee2 tyEliminee2 eliminator2) -> do
    -- CMOD dmu1 == dmu2
    addNewConstraint
      (JudTypeRel
        (divDeg dmu1 deg)
        (VarFromCtx <$> dmu1 :\\ gamma)
        (Pair3 tyEliminee1 tyEliminee2)
      )
      (Just parent)
      "Relating eliminees' types."
    addNewConstraint
      (JudTermRel
        (divDeg dmu1 deg)
        (VarFromCtx <$> dmu1 :\\ gamma)
        (Pair3 eliminee1 eliminee2)
        (Pair3 tyEliminee1 tyEliminee2)
      )
      (Just parent)
      "Relating eliminees."
    checkEliminatorRel parent deg gamma dmu1 eliminee1 eliminee2 tyEliminee1 tyEliminee2 eliminator1 eliminator2 ty1 ty2
  (TermElim _ _ _ _, _) -> tcFail parent "False."
  (TermMeta _ _, _) -> unreachable
  (TermWildcard, _) -> unreachable
  (TermQName _ _, _) -> unreachable
  (TermSmartElim _ _ _, _) -> unreachable
  (TermGoal _ _, _) -> unreachable
  (TermProblem t, _) -> tcFail parent "Nonsensical term."
  --(_, _) -> _checkTermNVRelNormal

checkTermRelNormal :: (MonadTC mode modty rel tc, Eq v) =>
  Constraint mode modty rel ->
  rel v ->
  Ctx (Pair3 Type) mode modty v Void ->
  Term mode modty v ->
  Term mode modty v ->
  Type mode modty v ->
  Type mode modty v ->
  tc ()
checkTermRelNormal parent deg gamma t1 t2 ty1 ty2 = case (t1, t2) of
        (Var3 v1, Var3 v2) -> if v1 == v2
          then return ()
          else tcFail parent "Cannot relate different variables."
        (Expr3 tnv1, Expr3 tnv2) -> checkTermNVRelNormal parent deg gamma tnv1 tnv2 ty1 ty2
        (Var3 _, Expr3 _) -> tcFail parent "Cannot relate variable and non-variable."
        (Expr3 _, Var3 _) -> tcFail parent "Cannot relate non-variable and variable."

tryToWHSolveTerm :: (MonadTC mode modty rel tc, Eq v) =>
  Constraint mode modty rel ->
  rel v ->
  Ctx (Pair3 Type) mode modty v Void ->
  Term mode modty v ->
  Term mode modty v ->
  [Int] ->
  Type mode modty v ->
  Type mode modty v ->
  tc ()
tryToWHSolveTerm parent deg gamma tBlocked tWHN metas tyBlocked tyWHN = case tBlocked of
  (Expr3 (TermMeta meta depcies)) -> _tryToWHSolveTerm
  _ -> blockOnMetas metas parent

checkTermRelNoEta :: (MonadTC mode modty rel tc, Eq v) =>
  Constraint mode modty rel ->
  rel v ->
  Ctx (Pair3 Type) mode modty v Void ->
  Term mode modty v ->
  Term mode modty v ->
  [Int] ->
  [Int] ->
  Type mode modty v ->
  Type mode modty v ->
  tc ()
checkTermRelNoEta parent deg gamma t1 t2 metasT1 metasT2 (Type ty1) (Type ty2) = case (metasT1, metasT2) of
  -- Both are whnormal
  ([], []) -> checkTermRelNormal parent deg gamma t1 t2 (Type ty1) (Type ty2)
  -- Only one is whnormal: whsolve or block
  (_, []) -> tryToWHSolveTerm parent deg gamma t1 t2 metasT1 (Type ty1) (Type ty2)
  ([], _) -> tryToWHSolveTerm parent deg gamma t2 t1 metasT2 (Type ty2) (Type ty1)
  -- Neither is whnormal: block
  (_, _) -> blockOnMetas (metasT1 ++ metasT2) parent

checkTermRelKnownTypes :: (MonadTC mode modty rel tc, Eq v) =>
  Constraint mode modty rel ->
  rel v ->
  Ctx (Pair3 Type) mode modty v Void ->
  Term mode modty v ->
  Term mode modty v ->
  [Int] ->
  [Int] ->
  Type mode modty v ->
  Type mode modty v ->
  tc ()
checkTermRelKnownTypes parent deg gamma t1 t2 metasT1 metasT2 (Type ty1) (Type ty2) = case (ty1, ty2) of
  (Expr3 (TermCons (ConsUniHS (Pi piBinding1))), Expr3 (TermCons (ConsUniHS (Pi piBinding2)))) -> do
    let seg1 = binding'segment piBinding1
    let dom2 = _segment'content $ binding'segment piBinding2
    let seg = over decl'content (\ dom1 -> Pair3 dom1 dom2) seg1
    let app1 = Expr3 $ TermElim
          (idModedModality $ VarWkn . unVarFromCtx <$> ctx'mode gamma)
          (VarWkn <$> t1) (Type $ VarWkn <$> ty1) (App $ Var3 VarLast)
    let app2 = Expr3 $ TermElim
          (idModedModality $ VarWkn . unVarFromCtx <$> ctx'mode gamma)
          (VarWkn <$> t2) (Type $ VarWkn <$> ty2) (App $ Var3 VarLast)
    addNewConstraint
      (JudTermRel
        (VarWkn <$> deg)
        (gamma :.. VarFromCtx <$> seg)
        (Pair3 app1 app2)
        (Pair3
          (Type $ binding'body piBinding1)
          (Type $ binding'body piBinding2)
        )
      )
      (Just parent)
      "Eta: Relating function bodies."
  (Expr3 (TermCons (ConsUniHS (Pi piBinding1))), _) ->
    tcFail parent "Types are presumed to be related."
  (Expr3 (TermCons (ConsUniHS (Sigma sigmaBinding1))), Expr3 (TermCons (ConsUniHS (Sigma sigmaBinding2)))) -> do
    -- CMOD am I dividing by the correct modality here?
    let dmu = _segment'modty $ binding'segment $ sigmaBinding1
    let d' = unVarFromCtx <$> ctx'mode gamma
    let fst1 = Expr3 $ TermElim (modedApproxLeftAdjointProj dmu d') t1 (Type ty1) Fst
    let fst2 = Expr3 $ TermElim (modedApproxLeftAdjointProj dmu d') t2 (Type ty2) Fst
    let snd1 = Expr3 $ TermElim (idModedModality d') t1 (Type t1) Snd
    let snd2 = Expr3 $ TermElim (idModedModality d') t2 (Type t2) Snd
    if not (sigmaHasEta dmu d')
      then checkTermRelNoEta  parent deg gamma t1 t2 metasT1 metasT2 (Type ty1) (Type ty2)
      else do
        addNewConstraint
          (JudTermRel
            (divDeg dmu deg)
            (VarFromCtx <$> dmu :\\ gamma)
            (Pair3 fst1 fst2)
            (Pair3
              (_segment'content $ binding'segment sigmaBinding1)
              (_segment'content $ binding'segment sigmaBinding2)
            )
          )
          (Just parent)
          "Eta: Relating first projections."
        addNewConstraint
          (JudTermRel
            deg
            gamma
            (Pair3 snd1 snd2)
            (Pair3
              (Type $ substLast3 fst1 $ binding'body sigmaBinding1)
              (Type $ substLast3 fst2 $ binding'body sigmaBinding2)
            )
          )
          (Just parent)
          "Eta: relating second projections"
  (Expr3 (TermCons (ConsUniHS (Sigma sigmaBinding1))), _) ->
    tcFail parent "Types are presumed to be related."
  (Expr3 (TermCons (ConsUniHS UnitType)), Expr3 (TermCons (ConsUniHS UnitType))) -> return ()
  (Expr3 (TermCons (ConsUniHS UnitType)), _) ->
    tcFail parent "Types are presumed to be related."
  (Expr3 (TermCons (ConsUniHS (BoxType boxSeg1))), Expr3 (TermCons (ConsUniHS (BoxType boxSeg2)))) -> do
    -- CMOD am I dividing by the correct modality here?
    let dmu = _segment'modty $ boxSeg1
    let d' = unVarFromCtx <$> ctx'mode gamma
    let unbox1 = Expr3 $ TermElim (modedApproxLeftAdjointProj dmu d') t1 (Type ty1) Unbox
    let unbox2 = Expr3 $ TermElim (modedApproxLeftAdjointProj dmu d') t2 (Type ty2) Unbox
    if not (sigmaHasEta dmu d')
      then checkTermRelNoEta  parent deg gamma t1 t2 metasT1 metasT2 (Type ty1) (Type ty2)
      else do
        addNewConstraint
          (JudTermRel
            (divDeg dmu deg)
            (VarFromCtx <$> dmu :\\ gamma)
            (Pair3 unbox1 unbox2)
            (Pair3
              (_segment'content boxSeg1)
              (_segment'content boxSeg2)
            )
          )
          (Just parent)
          "Eta: Relating box contents."
  (Expr3 (TermCons (ConsUniHS (BoxType boxSeg1))), _) ->
    tcFail parent "Types are presumed to be related."
  (_, _) -> checkTermRelNoEta parent deg gamma t1 t2 metasT1 metasT2 (Type ty1) (Type ty2)

checkTermRel :: (MonadTC mode modty rel tc, Eq v) =>
  Constraint mode modty rel ->
  rel v ->
  Ctx (Pair3 Type) mode modty v Void ->
  Term mode modty v ->
  Term mode modty v ->
  Type mode modty v ->
  Type mode modty v ->
  tc ()
checkTermRel parent deg gamma t1 t2 (Type ty1) (Type ty2) =
  -- Top-relatedness is always ok.
  if isTopDeg deg
    then return ()
    else do
      -- Weak-head-normalize everything
      (whnT1, metasT1) <- runWriterT $ whnormalize (fstCtx gamma) t1
      (whnT2, metasT2) <- runWriterT $ whnormalize (sndCtx gamma) t2
      (whnTy1, metasTy1) <- runWriterT $ whnormalize (fstCtx gamma) t1
      (whnTy2, metasTy2) <- runWriterT $ whnormalize (sndCtx gamma) t2
      whnparent <- Constraint
            (JudTermRel
              deg
              gamma
              (Pair3 whnT1 whnT2)
              (Pair3 (Type whnTy1) (Type whnTy2))
            )
            (Just parent)
            "Weak-head-normalize everything"
            <$> newConstraintID
      case (metasTy1, metasTy2) of
        -- Both types are whnormal
        ([], []) -> checkTermRelKnownTypes whnparent deg gamma whnT1 whnT2 metasT1 metasT2 (Type whnTy1) (Type whnTy2)
        -- Either type is not normal
        (_, _) -> blockOnMetas (metasTy1 ++ metasTy2) whnparent

      {-
      case (whnT1, whnT2) of
        -- If both sides are constructors: compare them
        (Expr3 (TermCons c1), Expr3 (TermCons c2)) ->
          checkConstructorTermRel whnparent deg gamma c1 c2 (Type whnTy1) (Type whnTy2)
        -- Otherwise, we want to eta-expand, so one of the types needs to be weak-head-normal
        (_, _) -> case (metasTy1, metasTy2) of
          -- Both types are whnormal
          ([], []) -> checkTermRelKnownTypes whnparent deg gamma whnT1 whnT2 metasT1 metasT2 (Type whnTy1) (Type whnTy2)
          -- Either type is not normal
          (_, _) -> blockOnMetas (metasT1 ++ metasT2 ++ metasTy1 ++ metasTy2) whnparent
          {-
          -- whnTy1 is whnormal
          ([], _) -> checkTermRelKnownType whnparent deg gamma whnT1 whnT2 metasT1 metasT2
                       (Type whnTy1) (Type whnTy2) (Type whnTy1)
          -- whnTy1 is blocked, but whnTy2 is normal
          (_, []) -> checkTermRelKnownType whnparent deg gamma whnT1 whnT2 metasT1 metasT2
                      (Type whnTy1) (Type whnTy2) (Type whnTy2)
          -- Both types are blocked. We may need to eta-expand but cannot. Hence, we cannot proceed.
          (_, _) -> blockOnMetas (metasT1 ++ metasT2 ++ metasTy1 ++ metasTy2) whnparent
          -}
      -}

      {- CANNOT COMPARE VARIABLES YET: what if we're in the unit type?
      case (whnT1, whnT2) of
        (Var3 v1, Var3 v2) -> if v1 == v2
          then return ()
          else tcFail parent "Cannot relate different variables."
        (Expr3 tnv1, Expr3 tnv2) -> _compareExprs
        (Var3 _, Expr3 _) -> tcFail parent "Cannot relate variable and non-variable."
        (Expr3 _, Var3 _) -> tcFail parent "Cannot relate non-variable and variable."
      -}

checkTypeRel :: (MonadTC mode modty rel tc, Eq v) =>
  Constraint mode modty rel ->
  rel v ->
  Ctx (Pair3 Type) mode modty v Void ->
  Type mode modty v ->
  Type mode modty v ->
  tc ()
checkTypeRel parent deg gamma (Type ty1) (Type ty2) =
  let uni = Type $ Expr3 $ TermCons $ ConsUniHS $ UniHS (unVarFromCtx <$> ctx'mode gamma) (Expr3 $ TermWildcard)
  in  addNewConstraint
        (JudTermRel
          deg
          gamma
          (Pair3 ty1 ty2)
          (Pair3 uni uni)
        )
        (Just parent)
        "Checking equality of types in a Hofmann-Streicher universe."
