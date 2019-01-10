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
import Menkar.TC.Inference.Solve

import Data.Void
import Control.Lens
import Data.Functor.Compose
import Control.Monad
import Control.Monad.Writer.Lazy

checkSegmentRel ::
  (MonadTC mode modty rel tc, DeBruijnLevel v) =>
  Constraint mode modty rel ->
  rel v ->
  Ctx (Pair3 Type) mode modty v Void ->
  Segment Type mode modty v ->
  Segment Type mode modty v ->
  tc ()
checkSegmentRel parent deg gamma seg1 seg2 = do
  -- CMOD check equality of modalities
  let d' = unVarFromCtx <$> ctx'mode gamma
  let uni = hs2type $ UniHS d' -- $ Expr3 TermWildcard
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

checkPiOrSigmaRel ::
  (MonadTC mode modty rel tc, DeBruijnLevel v) =>
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
    let uni = hs2type $ UniHS (VarWkn <$> d') -- $ Expr3 TermWildcard
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

checkUniHSConstructorRel ::
  (MonadTC mode modty rel tc, DeBruijnLevel v) =>
  Constraint mode modty rel ->
  rel v ->
  Ctx (Pair3 Type) mode modty v Void ->
  UniHSConstructor mode modty v ->
  UniHSConstructor mode modty v ->
  Type mode modty v ->
  Type mode modty v ->
  tc ()
checkUniHSConstructorRel parent deg gamma t1 t2 ty1 ty2 = case (t1, t2) of
  (UniHS d1 {-lvl1-}, UniHS d2 {-lvl2-}) -> return ()
    {-do
    let nat = hs2type $ NatType
    addNewConstraint
      (JudTermRel
        (divDeg irrModedModality deg)
        (irrModedModality :\\ gamma)
        (Pair3 lvl1 lvl2)
        (Pair3 nat nat)
      )
      (Just parent)
      "Relating levels."-}
  (UniHS _, _) -> tcFail parent "False."
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

checkConstructorTermRel :: forall mode modty rel tc v .
  (MonadTC mode modty rel tc, DeBruijnLevel v) =>
  Constraint mode modty rel ->
  rel v ->
  Ctx (Pair3 Type) mode modty v Void ->
  ConstructorTerm mode modty v ->
  ConstructorTerm mode modty v ->
  Type mode modty v ->
  Type mode modty v ->
  [Int] ->
  [Int] ->
  tc ()
checkConstructorTermRel parent deg gamma t1 t2 ty1 ty2 metasTy1 metasTy2 = case (t1, t2) of
  (ConsUniHS c1, ConsUniHS c2) -> checkUniHSConstructorRel parent deg gamma c1 c2 ty1 ty2
  (ConsUniHS _, _) -> tcFail parent "False."
  -- Encountering a lambda is not possible: it's well-typed, so the type is a Pi-type, so eta-expansion has fired.
  (Lam binding, _) -> _fixallofthis -- tcFail parent "LHS is presumed to be well-typed."
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

checkDependentEliminatorRel :: forall mode modty rel tc v .
  (MonadTC mode modty rel tc, DeBruijnLevel v) =>
  Constraint mode modty rel ->
  rel v ->
  Ctx (Pair3 Type) mode modty v Void ->
  ModedModality mode modty v {-^ Modality by which the eliminee is eliminated. -} ->
  Term mode modty v ->
  Term mode modty v ->
  Type mode modty v ->
  Type mode modty v ->
  NamedBinding Type mode modty v ->
  NamedBinding Type mode modty v ->
  DependentEliminator mode modty v ->
  DependentEliminator mode modty v ->
  Type mode modty v {-^ May not be whnormal. -} ->
  Type mode modty v {-^ May not be whnormal. -} ->
  tc ()
checkDependentEliminatorRel parent deg gamma dmu
  eliminee1 eliminee2
  tyEliminee1 tyEliminee2
  motive1 motive2
  clauses1 clauses2
  ty1 ty2 =
    case (clauses1, clauses2) of
      (ElimSigma pairClause1, ElimSigma pairClause2) -> case (tyEliminee1, tyEliminee2) of
        (Type (Expr3 (TermCons (ConsUniHS (Sigma sigmaBinding1)))),
         Type (Expr3 (TermCons (ConsUniHS (Sigma sigmaBinding2))))) -> do
          let segFst :: Segment (Pair3 Type) _ _ _
              segFst = Declaration
                         (DeclNameSegment $ _namedBinding'name pairClause1)
                         (compModedModality dmu (_segment'modty $ binding'segment $ sigmaBinding1))
                         Explicit
                         (Pair3
                           (_segment'content $ binding'segment $ sigmaBinding1)
                           (_segment'content $ binding'segment $ sigmaBinding2)
                         )
          let segSnd :: Segment (Pair3 Type) _ _ (VarExt _)
              segSnd = Declaration
                         (DeclNameSegment $ _namedBinding'name $ _namedBinding'body pairClause1)
                         (VarWkn <$> dmu)
                         Explicit
                         (Pair3
                           (Type $ binding'body sigmaBinding1)
                           (Type $ binding'body sigmaBinding2)
                         )
          let subst' :: Binding Type Term _ _ _ -> VarExt _ -> Term _ _ (VarExt (VarExt _))
              subst' sigmaBinding VarLast =
                Expr3 $ TermCons $ Pair (VarWkn . VarWkn <$> sigmaBinding) (Var3 $ VarWkn VarLast) (Var3 VarLast)
              subst' sigmaBinding (VarWkn v) = Var3 $ VarWkn $ VarWkn $ v
              subst :: Binding Type Term _ _ _ -> Type _ _ (VarExt _) -> Type _ _ (VarExt (VarExt _))
              subst sigmaBinding = swallow . fmap (subst' sigmaBinding)
          addNewConstraint
            (JudTermRel
              (VarWkn . VarWkn <$> deg)
              (gamma :.. VarFromCtx <$> segFst :.. VarFromCtx <$> segSnd)
              (Pair3
                (_namedBinding'body $ _namedBinding'body $ pairClause1)
                (_namedBinding'body $ _namedBinding'body $ pairClause2)
              )
              (Pair3
                (subst sigmaBinding1 $ _namedBinding'body motive1)
                (subst sigmaBinding2 $ _namedBinding'body motive2)
              )
            )
            (Just parent)
            "Relating elimination clauses for the pair constructor."
        (_, _) -> unreachable
                  -- It is an error to construct an elimination term where the eliminee's type does not
                  -- match the elimination clauses.
      (ElimSigma _, _) -> tcFail parent "Terms are presumed to be well-typed in related types."
      (ElimBox boxClause1, ElimBox boxClause2) -> case (tyEliminee1, tyEliminee2) of
        (Type (Expr3 (TermCons (ConsUniHS (BoxType boxSeg1)))),
         Type (Expr3 (TermCons (ConsUniHS (BoxType boxSeg2))))) -> do
           let segContent :: Segment (Pair3 Type) _ _ _
               segContent = Declaration
                              (DeclNameSegment $ _namedBinding'name boxClause1)
                              (compModedModality dmu (_segment'modty boxSeg1))
                              Explicit
                              (Pair3
                                (_segment'content boxSeg1)
                                (_segment'content boxSeg2)
                              )
           let subst :: Segment Type _ _ _ -> VarExt _ -> Term _ _ (VarExt _)
               subst boxSeg VarLast = Expr3 $ TermCons $ ConsBox (VarWkn <$> boxSeg) $ Var3 VarLast
               subst boxSeg (VarWkn v) = Var3 $ VarWkn v
           addNewConstraint
             (JudTermRel
               (VarWkn <$> deg)
               (gamma :.. VarFromCtx <$> segContent)
               (Pair3
                 (_namedBinding'body $ boxClause1)
                 (_namedBinding'body $ boxClause2)
               )
               (Pair3
                 (swallow $ subst boxSeg1 <$> (_namedBinding'body motive1))
                 (swallow $ subst boxSeg2 <$> (_namedBinding'body motive2))
               )
             )
             (Just parent)
             "Relating elimination clauses for the box constructor."
        (_, _) -> unreachable
                  -- It is an error to construct an elimination term where the eliminee's type does not
                  -- match the elimination clauses.
      (ElimBox _, _) -> tcFail parent "Terms are presumed to be well-typed in related types."
      (ElimEmpty, ElimEmpty) -> return ()
      (ElimEmpty, _) -> tcFail parent "Terms are presumed to be well-typed in related types."
      (ElimNat clauseZero1 clauseSuc1, ElimNat clauseZero2 clauseSuc2) -> do
        let substZ :: VarExt v -> Term mode modty v
            substZ VarLast = Expr3 $ TermCons $ ConsZero
            substZ (VarWkn v) = Var3 v
        addNewConstraint
          (JudTermRel
            deg
            gamma
            (Pair3 clauseZero1 clauseZero2)
            (Pair3
              (swallow $ substZ <$> _namedBinding'body motive1)
              (swallow $ substZ <$> _namedBinding'body motive2)
            )
          )
          (Just parent)
          "Relating zero clauses."
        let nat = (Type $ Expr3 $ TermCons $ ConsUniHS $ NatType)
        let segPred :: Segment (Pair3 Type) _ _ _
            segPred = Declaration
                        (DeclNameSegment $ _namedBinding'name clauseSuc1)
                        dmu
                        Explicit
                        (Pair3 nat nat)
        let segHyp :: Segment (Pair3 Type) _ _ (VarExt _)
            segHyp = Declaration
                       (DeclNameSegment $ _namedBinding'name $ _namedBinding'body clauseSuc1)
                       (idModedModality $ VarWkn . unVarFromCtx <$> ctx'mode gamma)
                       Explicit
                       (Pair3
                         (_namedBinding'body motive1)
                         (_namedBinding'body motive2)
                       )
        let substS :: VarExt v -> Term mode modty (VarExt (VarExt v))
            substS VarLast = Expr3 $ TermCons $ ConsSuc $ Var3 $ VarWkn VarLast
            substS (VarWkn v) = Var3 $ VarWkn $ VarWkn v
        addNewConstraint
          (JudTermRel
            (VarWkn . VarWkn <$> deg)
            (gamma :.. VarFromCtx <$> segPred :.. VarFromCtx <$> segHyp)
            (Pair3
              (_namedBinding'body $ _namedBinding'body $ clauseSuc1)
              (_namedBinding'body $ _namedBinding'body $ clauseSuc2)
            )
            (Pair3
              (swallow $ substS <$> _namedBinding'body motive1)
              (swallow $ substS <$> _namedBinding'body motive2)
            )
          )
          (Just parent)
          "Relating successor clauses."
      (ElimNat _ _, _) -> tcFail parent "Terms are presumed to be well-typed in related types."
      --(_, _) -> _checkDependentEliminatorRel
      
checkEliminatorRel ::
  (MonadTC mode modty rel tc, DeBruijnLevel v) =>
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
  Type mode modty v {-^ May not be whnormal. -} ->
  Type mode modty v {-^ May not be whnormal. -} ->
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
        (Pair3 (_namedBinding'body motive1) (_namedBinding'body motive2))
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

{-| Relate a constructor-term with a whnormal non-constructor term.
-}
checkTermNVRelEta :: (MonadTC mode modty rel tc, DeBruijnLevel v) =>
  Constraint mode modty rel ->
  rel v ->
  Ctx (Pair3 Type) mode modty v Void ->
  ConstructorTerm mode modty v ->
  TermNV mode modty v ->
  Type mode modty v ->
  Type mode modty v ->
  [Int] ->
  [Int] ->
  tc ()
checkTermNVRelEta parent deg gamma c1 t2 (Type ty1) (Type ty2) metasTy1 metasTy2 = case c1 of
  ConsUniHS _ -> tcFail parent "False."
  Lam lambdaBinding1 -> case (metasTy1, metasTy2, ty1, ty2) of
    ([], [], Expr3 (TermCons (ConsUniHS (Pi piBinding1))), Expr3 (TermCons (ConsUniHS (Pi piBinding2)))) -> do
      let seg1 = binding'segment lambdaBinding1
      let dom2 = _segment'content $ binding'segment piBinding2
      let seg = over decl'content (\ dom1 -> Pair3 dom1 dom2) seg1
      let app1 = binding'body lambdaBinding1
      let app2 = Expr3 $ TermElim
            (idModedModality $ VarWkn . unVarFromCtx <$> ctx'mode gamma)
            (VarWkn <$> Expr3 t2) (VarWkn <$> Pi piBinding2) (App $ Var3 VarLast)
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
    ([], [], _, _) -> tcFail parent "Both hands are presumed to be well-typed."
    (_, _, _, _) -> tcBlock parent "Need to analyze function types."  
  Pair sigmaBinding1' tFst1 tSnd1 -> do
    -- CMOD am I dividing by the correct modality here?
    let dmu = _segment'modty $ binding'segment $ sigmaBinding1'
    let d' = unVarFromCtx <$> ctx'mode gamma
    when (not (sigmaHasEta dmu d')) $ tcFail parent "False. (This sigma-type has no eta-rule.)"
    case (metasTy1, metasTy2, ty1, ty2) of
      ([], [], Expr3 (TermCons (ConsUniHS (Sigma sigmaBinding1))), Expr3 (TermCons (ConsUniHS (Sigma sigmaBinding2)))) -> do
        let tFst2 = Expr3 $ TermElim (modedApproxLeftAdjointProj dmu d') (Expr3 t2) (Sigma sigmaBinding2) Fst
        let tSnd2 = Expr3 $ TermElim (idModedModality d') (Expr3 t2) (Sigma sigmaBinding2) Snd
        addNewConstraint
          (JudTermRel
            (divDeg dmu deg)
            (VarFromCtx <$> dmu :\\ gamma)
            (Pair3 tFst1 tFst2)
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
            (Pair3 tSnd1 tSnd2)
            (Pair3
              (Type $ substLast3 tFst1 $ binding'body sigmaBinding1)
              (Type $ substLast3 tFst2 $ binding'body sigmaBinding2)
            )
          )
          (Just parent)
          "Eta: relating second projections"
      ([], [], _, _) -> tcFail parent "Both hands are presumed to be well-typed."
      (_, _, _, _) -> tcBlock parent "Need to analyze sigma types."
  ConsUnit -> return ()
  ConsBox boxSeg1' tUnbox1 -> do
    -- CMOD am I dividing by the correct modality here?
    let dmu = _segment'modty $ boxSeg1'
    let d' = unVarFromCtx <$> ctx'mode gamma
    when (not (sigmaHasEta dmu d')) $ tcFail parent "False. (This box-type has no eta-rule.)"
    case (metasTy1, metasTy2, ty1, ty2) of
      ([], [], Expr3 (TermCons (ConsUniHS (BoxType boxSeg1))), Expr3 (TermCons (ConsUniHS (BoxType boxSeg2)))) -> do
        let tUnbox2 = Expr3 $ TermElim (modedApproxLeftAdjointProj dmu d') (Expr3 t2) (BoxType boxSeg2) Unbox
        addNewConstraint
          (JudTermRel
            (divDeg dmu deg)
            (VarFromCtx <$> dmu :\\ gamma)
            (Pair3 tUnbox1 tUnbox2)
            (Pair3
              (_segment'content $ boxSeg1)
              (_segment'content $ boxSeg2)
            )
          )
          (Just parent)
          "Eta: Relating box contents."
      ([], [], _, _) -> tcFail parent "Both hands are presumed to be well-typed."
      (_, _, _, _) -> tcBlock parent "Need to analyze sigma types."
  ConsZero -> tcFail parent "False."
  ConsSuc t -> tcFail parent "False."

{-| Relate 2 non-variable whnormal terms.
-}
checkTermNVRelWHNTerms :: (MonadTC mode modty rel tc, DeBruijnLevel v) =>
  Constraint mode modty rel ->
  rel v ->
  Ctx (Pair3 Type) mode modty v Void ->
  TermNV mode modty v ->
  TermNV mode modty v ->
  Type mode modty v ->
  Type mode modty v ->
  [Int] ->
  [Int] ->
  tc ()
checkTermNVRelWHNTerms parent deg gamma t1 t2 ty1 ty2 metasTy1 metasTy2 = case (t1, t2) of
  (TermCons c1, TermCons c2) -> checkConstructorTermRel parent deg gamma c1 c2 ty1 ty2 metasTy1 metasTy2
  (TermCons c1, _) -> checkTermNVRelEta parent deg          gamma  c1 t2 ty1 ty2 metasTy1 metasTy2
  (_, TermCons c2) -> checkTermNVRelEta parent deg (flipCtx gamma) c2 t1 ty2 ty1 metasTy2 metasTy1
  (TermElim dmu1 eliminee1 tyEliminee1 eliminator1, TermElim dmu2 eliminee2 tyEliminee2 eliminator2) -> do
    let tyEliminee1' = Type $ Expr3 $ TermCons $ ConsUniHS $ tyEliminee1
    let tyEliminee2' = Type $ Expr3 $ TermCons $ ConsUniHS $ tyEliminee2
    -- CMOD dmu1 == dmu2
    addNewConstraint
      (JudTypeRel
        (divDeg dmu1 deg)
        (VarFromCtx <$> dmu1 :\\ gamma)
        (Pair3 tyEliminee1' tyEliminee2')
      )
      (Just parent)
      "Relating eliminees' types."
    addNewConstraint
      (JudTermRel
        (divDeg dmu1 deg)
        (VarFromCtx <$> dmu1 :\\ gamma)
        (Pair3 eliminee1 eliminee2)
        (Pair3 tyEliminee1' tyEliminee2')
      )
      (Just parent)
      "Relating eliminees."
    checkEliminatorRel parent deg gamma dmu1 eliminee1 eliminee2 tyEliminee1' tyEliminee2' eliminator1 eliminator2 ty1 ty2
  (TermElim _ _ _ _, _) -> tcFail parent "False."
  (TermMeta _ _, _) -> unreachable
  (TermWildcard, _) -> unreachable
  (TermQName _ _, _) -> unreachable
  (TermSmartElim _ _ _, _) -> unreachable
  (TermGoal _ _, _) -> unreachable
  (TermProblem t, _) -> tcFail parent "Nonsensical term."
  --(_, _) -> _checkTermNVRelNormal

{-| Relate 2 whnormal terms.
-}
checkTermRelWHNTerms :: (MonadTC mode modty rel tc, DeBruijnLevel v) =>
  Constraint mode modty rel ->
  rel v ->
  Ctx (Pair3 Type) mode modty v Void ->
  Term mode modty v ->
  Term mode modty v ->
  Type mode modty v ->
  Type mode modty v ->
  [Int] ->
  [Int] ->
  tc ()
checkTermRelWHNTerms parent deg gamma t1 t2 ty1 ty2 metasTy1 metasTy2 = case (t1, t2) of
        (Var3 v1, Var3 v2) -> if v1 == v2
          then return ()
          else tcFail parent "Cannot relate different variables."
        (Expr3 tnv1, Expr3 tnv2) -> checkTermNVRelWHNTerms parent deg gamma tnv1 tnv2 ty1 ty2 metasTy1 metasTy2
        (Var3 _, Expr3 _) -> tcFail parent "Cannot relate variable and non-variable."
        (Expr3 _, Var3 _) -> tcFail parent "Cannot relate non-variable and variable."

{-
checkTermRelWHN :: (MonadTC mode modty rel tc, DeBruijnLevel v) =>
  Constraint mode modty rel ->
  rel v ->
  Ctx (Pair3 Type) mode modty v Void ->
  Term mode modty v ->
  Term mode modty v ->
  Type mode modty v ->
  Type mode modty v ->
  tc ()
checkTermRelWHN parent deg gamma t1 t2 (Type ty1) (Type ty2) = case (ty1, ty2) of
  -- Pi types: eta-expand
  (Expr3 (TermCons (ConsUniHS (Pi piBinding1))), Expr3 (TermCons (ConsUniHS (Pi piBinding2)))) -> do
    let seg1 = binding'segment piBinding1
    let dom2 = _segment'content $ binding'segment piBinding2
    let seg = over decl'content (\ dom1 -> Pair3 dom1 dom2) seg1
    let app1 = Expr3 $ TermElim
          (idModedModality $ VarWkn . unVarFromCtx <$> ctx'mode gamma)
          (VarWkn <$> t1) (VarWkn <$> Pi piBinding1) (App $ Var3 VarLast)
    let app2 = Expr3 $ TermElim
          (idModedModality $ VarWkn . unVarFromCtx <$> ctx'mode gamma)
          (VarWkn <$> t2) (VarWkn <$> Pi piBinding2) (App $ Var3 VarLast)
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
  -- Sigma types: eta expand if allowed
  (Expr3 (TermCons (ConsUniHS (Sigma sigmaBinding1))), Expr3 (TermCons (ConsUniHS (Sigma sigmaBinding2)))) -> do
    -- CMOD am I dividing by the correct modality here?
    let dmu = _segment'modty $ binding'segment $ sigmaBinding1
    let d' = unVarFromCtx <$> ctx'mode gamma
    let fst1 = Expr3 $ TermElim (modedApproxLeftAdjointProj dmu d') t1 (Sigma sigmaBinding1) Fst
    let fst2 = Expr3 $ TermElim (modedApproxLeftAdjointProj dmu d') t2 (Sigma sigmaBinding2) Fst
    let snd1 = Expr3 $ TermElim (idModedModality d') t1 (Sigma sigmaBinding1) Snd
    let snd2 = Expr3 $ TermElim (idModedModality d') t2 (Sigma sigmaBinding2) Snd
    if not (sigmaHasEta dmu d')
      then checkTermRelNoEta  parent deg gamma t1 t2 (Type ty1) (Type ty2)
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
  -- Unit type: eta-expand
  (Expr3 (TermCons (ConsUniHS UnitType)), Expr3 (TermCons (ConsUniHS UnitType))) -> return ()
  (Expr3 (TermCons (ConsUniHS UnitType)), _) ->
    tcFail parent "Types are presumed to be related."
  -- Box type: eta-expand
  (Expr3 (TermCons (ConsUniHS (BoxType boxSeg1))), Expr3 (TermCons (ConsUniHS (BoxType boxSeg2)))) -> do
    -- CMOD am I dividing by the correct modality here?
    let dmu = _segment'modty $ boxSeg1
    let d' = unVarFromCtx <$> ctx'mode gamma
    let unbox1 = Expr3 $ TermElim (modedApproxLeftAdjointProj dmu d') t1 (BoxType boxSeg1) Unbox
    let unbox2 = Expr3 $ TermElim (modedApproxLeftAdjointProj dmu d') t2 (BoxType boxSeg2) Unbox
    if not (sigmaHasEta dmu d')
      then checkTermRelNoEta  parent deg gamma t1 t2 (Type ty1) (Type ty2)
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
  (_, _) -> checkTermRelNoEta parent deg gamma t1 t2 (Type ty1) (Type ty2)

checkTermRelWHNTerms :: (MonadTC mode modty rel tc, DeBruijnLevel v) =>
  Constraint mode modty rel ->
  rel v ->
  Ctx (Pair3 Type) mode modty v Void ->
  Term mode modty v ->
  Term mode modty v ->
  Type mode modty v ->
  Type mode modty v ->
  [Int] ->
  [Int] ->
  tc ()
checkTermRelWHNTerms parent deg gamma t1 t2 (Type ty1) (Type ty2) metasTy1 metasTy2 = do
  case (metasTy1, metasTy2) of
    -- Both types are whnormal
    ([], []) -> checkTermRelWHN parent deg gamma t1 t2 (Type ty1) (Type ty2)
    -- Either type is not normal
    (_, _) -> tcBlock parent "Need to weak-head-normalize types to tell whether I should use eta-expansion."
-}

checkTermRel :: (MonadTC mode modty rel tc, DeBruijnLevel v) =>
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
      --purposefully shadowing (redefining)
      (t1, metasT1) <- runWriterT $ whnormalize parent (fstCtx gamma) t1 "Weak-head-normalizing first term."
      (t2, metasT2) <- runWriterT $ whnormalize parent (sndCtx gamma) t2 "Weak-head-normalizing second term."
      (ty1, metasTy1) <- runWriterT $ whnormalize parent (fstCtx gamma) ty1 "Weak-head-normalizing first type."
      (ty2, metasTy2) <- runWriterT $ whnormalize parent (sndCtx gamma) ty2 "Weak-head-normalizing second type."
      parent <- defConstraint
            (JudTermRel
              deg
              gamma
              (Pair3 t1 t2)
              (Pair3 (Type ty1) (Type ty2))
            )
            (Just parent)
            "Weak-head-normalize everything"

      case (metasT1, metasT2) of
        -- Both are whnormal
        ([], []) -> checkTermRelWHNTerms parent deg gamma t1 t2 (Type ty1) (Type ty2) metasTy1 metasTy2
        -- Only one is whnormal: whsolve or block
        (_, []) -> tryToSolveTerm parent deg          gamma  t1 t2 metasT1 (Type ty1) (Type ty2) metasTy1 metasTy2
        ([], _) -> tryToSolveTerm parent deg (flipCtx gamma) t2 t1 metasT2 (Type ty2) (Type ty1) metasTy1 metasTy2
        -- Neither is whnormal: block
        (_, _) -> tcBlock parent "Cannot solve relation: both sides are blocked on a meta-variable."

      {-
      case (whnT1, whnT2) of
        -- If both sides are constructors: compare them
        (Expr3 (TermCons c1), Expr3 (TermCons c2)) ->
          checkConstructorTermRel whnparent deg gamma c1 c2 (Type whnTy1) (Type whnTy2)
        -- Otherwise, we want to eta-expand, so one of the types needs to be weak-head-normal
        (_, _) -> case (metasTy1, metasTy2) of
          -- Both types are whnormal
          ([], []) -> checkTermRelWHNTypes whnparent deg gamma whnT1 whnT2 metasT1 metasT2 (Type whnTy1) (Type whnTy2)
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

checkTypeRel :: (MonadTC mode modty rel tc, DeBruijnLevel v) =>
  Constraint mode modty rel ->
  rel v ->
  Ctx (Pair3 Type) mode modty v Void ->
  Type mode modty v ->
  Type mode modty v ->
  tc ()
checkTypeRel parent deg gamma (Type ty1) (Type ty2) =
  let uni = Type $ Expr3 $ TermCons $ ConsUniHS $ UniHS (unVarFromCtx <$> ctx'mode gamma) --(Expr3 $ TermWildcard)
  in  addNewConstraint
        (JudTermRel
          deg
          gamma
          (Pair3 ty1 ty2)
          (Pair3 uni uni)
        )
        (Just parent)
        "Checking relatedness of types in a Hofmann-Streicher universe."
