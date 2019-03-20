module Menkar.TC.Rel where

import Menkar.System.Fine
import Menkar.System.WHN
import Menkar.System.TC
import Menkar.Fine.Syntax
import Menkar.Basic.Context
import Menkar.Fine.Context
import Menkar.Fine.Judgement
import Menkar.Fine.LookupQName
import qualified Menkar.Raw.Syntax as Raw
import Menkar.Monad.Monad
import Control.Exception.AssertFalse
import Menkar.WHN
--import Menkar.TC.Solve

import Data.Void
import Control.Lens
import Data.Functor.Compose
import Control.Monad
import Control.Monad.Writer.Lazy

isBlockedOrMeta :: Term sys v -> [Int] -> Bool
isBlockedOrMeta (Expr2 (TermMeta _ _ _ _)) _ = True
isBlockedOrMeta _ (_:_) = True
isBlockedOrMeta _ [] = False

checkSegmentRel ::
  (SysTC sys, MonadTC sys tc, DeBruijnLevel v) =>
  Constraint sys ->
  Degree sys v ->
  Ctx (Twice2 Type) sys v Void ->
  Segment Type sys v ->
  Segment Type sys v ->
  tc ()
checkSegmentRel parent deg gamma seg1 seg2 = do
  let d' = unVarFromCtx <$> ctx'mode gamma
  let uni = hs2type $ UniHS d' -- $ Expr2 TermWildcard
  addNewConstraint
    (JudModedModalityRel ModEq
      (crispModedModality :\\ gamma)
      (_segment'modty seg1)
      (_segment'modty seg2)
      d'
    )
    (Just parent)
    "Relating modalities."
  addNewConstraint
    (JudTermRel
      (Eta True)
      deg
      gamma
      (Twice2
        (unType $ _segment'content seg1)
        (unType $ _segment'content seg2)
      )
      (Twice2 uni uni)
    )
    (Just parent)
    "Relating domains."      

checkPiOrSigmaRel ::
  (SysTC sys, MonadTC sys tc, DeBruijnLevel v) =>
  Constraint sys ->
  Degree sys v ->
  Ctx (Twice2 Type) sys v Void ->
  Binding Type Term sys v ->
  Binding Type Term sys v ->
  UniHSConstructor sys v ->
  UniHSConstructor sys v ->
  tc ()
checkPiOrSigmaRel parent deg gamma binding1 binding2 ty1 ty2 = do
    let seg1 = (binding'segment binding1)
    let seg2 = (binding'segment binding2)
    let dom2 = _segment'content $ binding'segment binding2
    let seg = over decl'content (\ dom1 -> Twice2 dom1 dom2) seg1
    let d' = unVarFromCtx <$> ctx'mode gamma
    let uni = hs2type $ UniHS (VarWkn <$> d') -- $ Expr2 TermWildcard
    checkSegmentRel parent deg gamma seg1 seg2
    addNewConstraint
      (JudTermRel
        (Eta True)
        (VarWkn <$> deg)
        (gamma :.. VarFromCtx <$> seg)
        (Twice2
          (binding'body binding1)
          (binding'body binding2)
        )
        (Twice2 uni uni)
      )
      (Just parent)
      "Relating codomains."

checkUniHSConstructorRel ::
  (SysTC sys, MonadTC sys tc, DeBruijnLevel v) =>
  Constraint sys ->
  Degree sys v ->
  Ctx (Twice2 Type) sys v Void ->
  UniHSConstructor sys v ->
  UniHSConstructor sys v ->
  UniHSConstructor sys v ->
  UniHSConstructor sys v ->
  tc ()
checkUniHSConstructorRel parent deg gamma t1 t2 ty1 ty2 = case (t1, t2) of
  (UniHS d1 {-lvl1-}, UniHS d2 {-lvl2-}) -> return ()
    {-do
    let nat = hs2type $ NatType
    addNewConstraint
      (JudTermRel
        (divDeg irrModedModality deg)
        (irrModedModality :\\ gamma)
        (Twice2 lvl1 lvl2)
        (Twice2 nat nat)
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
  (EqType tyAmbient1 tL1 tR1, EqType tyAmbient2 tL2 tR2) -> do
    addNewConstraint
      (JudTypeRel deg gamma (Twice2 tyAmbient1 tyAmbient2))
      (Just parent)
      "Relating ambient types."
    addNewConstraint
      (JudTermRel (Eta True) deg gamma (Twice2 tL1 tL2) (Twice2 tyAmbient1 tyAmbient2))
      (Just parent)
      "Relating left equands."
    addNewConstraint
      (JudTermRel (Eta True) deg gamma (Twice2 tR1 tR2) (Twice2 tyAmbient1 tyAmbient2))
      (Just parent)
      "Relating right equands."
  (EqType _ _ _, _) -> tcFail parent "False."
  --(_, _) -> _checkUniHSConstructorRel

--------------------------------------------------------
-- NO ETA --
--------------------------------------------------------

checkConstructorTermRelNoEta :: forall sys tc v .
  (SysTC sys, MonadTC sys tc, DeBruijnLevel v) =>
  Constraint sys ->
  Degree sys v ->
  Ctx (Twice2 Type) sys v Void ->
  ConstructorTerm sys v ->
  ConstructorTerm sys v ->
  UniHSConstructor sys v ->
  UniHSConstructor sys v ->
  tc ()
checkConstructorTermRelNoEta parent deg gamma t1 t2 ty1 ty2 = case (t1, t2) of
  (ConsUniHS c1, ConsUniHS c2) -> checkUniHSConstructorRel parent deg gamma c1 c2 ty1 ty2
  (ConsUniHS _, _) -> tcFail parent "False."
  --(Lam _, Lam _) -> checkTermRelEta parent deg gamma t1 (Expr2 $ TermCons t2) ty1 ty2 metasTy1 metasTy2
  (Lam _, _) -> unreachable --tcFail parent "False."
  (Pair sigmaBinding1 fst1 snd1, Pair sigmaBinding2 fst2 snd2) -> do
    let dmu = _segment'modty $ binding'segment $ sigmaBinding1
        dom1 = _segment'content $ binding'segment $ sigmaBinding1
        dom2 = _segment'content $ binding'segment $ sigmaBinding2
        cod1 = binding'body sigmaBinding1
        cod2 = binding'body sigmaBinding2
    addNewConstraint
      (JudTermRel
        (Eta True)
        (divDeg dmu deg)
        (VarFromCtx <$> dmu :\\ gamma)
        (Twice2 fst1 fst2)
        (Twice2 dom1 dom2)
      )
      (Just parent)
      "Relating first components."
    addNewConstraint
      (JudTermRel
        (Eta True)
        deg
        gamma
        (Twice2 snd1 snd2)
        (Twice2
          (Type $ substLast2 fst1 $ cod1)
          (Type $ substLast2 fst2 $ cod2)
        )
      )
      (Just parent)
      "Relating second components."
  (Pair _ _ _, _) -> tcFail parent "False."
  --(Pair _ _ _, _) -> checkTermRelEta parent deg          gamma  t1 (Expr2 $ TermCons t2) ty1 ty2 metasTy1 metasTy2
  --(_, Pair _ _ _) -> checkTermRelEta parent deg (flipCtx gamma) t2 (Expr2 $ TermCons t1) ty2 ty1 metasTy2 metasTy1
  --(ConsUnit, ConsUnit) -> return ()
  (ConsUnit, _) -> unreachable --tcFail parent "False."
  (ConsBox boxSeg1 unbox1, ConsBox boxSeg2 unbox2) -> do
    let dmu = _segment'modty $ boxSeg1
        dom1 = _segment'content $ boxSeg1
        dom2 = _segment'content $ boxSeg2
    addNewConstraint
      (JudTermRel
        (Eta True)
        (divDeg dmu deg)
        (VarFromCtx <$> dmu :\\ gamma)
        (Twice2 unbox1 unbox2)
        (Twice2 dom1 dom2)
      )
      (Just parent)
      "Relating box contents."
  (ConsBox _ _, _) -> tcFail parent "False."
  --(_, ConsBox _ _) -> checkTermRelEta parent deg (flipCtx gamma) t2 (Expr2 $ TermCons t1) ty2 ty1 metasTy2 metasTy1
  (ConsZero, ConsZero) -> return ()
  (ConsZero, _) -> tcFail parent "False."
  (ConsSuc n1, ConsSuc n2) -> do
    let nat = Type $ Expr2 $ TermCons $ ConsUniHS $ NatType
    addNewConstraint
      (JudTermRel (Eta True) deg gamma (Twice2 n1 n2) (Twice2 nat nat))
      (Just parent)
      "Relating predecessors."
  (ConsSuc _, _) -> tcFail parent "False."
  (ConsRefl, ConsRefl) -> return ()
  (ConsRefl, _) -> tcFail parent "False."
  --(_, _) -> _checkConstructorTermRelNoEta

checkDependentEliminatorRelNoEta :: forall sys tc v .
  (SysTC sys, MonadTC sys tc, DeBruijnLevel v) =>
  Constraint sys ->
  Degree sys v ->
  Ctx (Twice2 Type) sys v Void ->
  ModedModality sys v {-^ Modality by which the eliminee is eliminated. -} ->
  Term sys v ->
  Term sys v ->
  UniHSConstructor sys v ->
  UniHSConstructor sys v ->
  NamedBinding Type sys v ->
  NamedBinding Type sys v ->
  DependentEliminator sys v ->
  DependentEliminator sys v ->
  UniHSConstructor sys v ->
  UniHSConstructor sys v ->
  tc ()
checkDependentEliminatorRelNoEta parent deg gamma dmu
  eliminee1 eliminee2
  tyEliminee1 tyEliminee2
  motive1 motive2
  clauses1 clauses2
  ty1 ty2 =
    case (clauses1, clauses2) of
      (ElimSigma pairClause1, ElimSigma pairClause2) -> case (tyEliminee1, tyEliminee2) of
        (Sigma sigmaBinding1, Sigma sigmaBinding2) -> do
          let segFst :: Segment (Twice2 Type) _ _
              segFst = Declaration
                         (DeclNameSegment $ _namedBinding'name pairClause1)
                         (compModedModality dmu (_segment'modty $ binding'segment $ sigmaBinding1))
                         Explicit
                         (Twice2
                           (_segment'content $ binding'segment $ sigmaBinding1)
                           (_segment'content $ binding'segment $ sigmaBinding2)
                         )
          let segSnd :: Segment (Twice2 Type) _ (VarExt _)
              segSnd = Declaration
                         (DeclNameSegment $ _namedBinding'name $ _namedBinding'body pairClause1)
                         (VarWkn <$> dmu)
                         Explicit
                         (Twice2
                           (Type $ binding'body sigmaBinding1)
                           (Type $ binding'body sigmaBinding2)
                         )
          let subst' :: Binding Type Term _ _ -> VarExt _ -> Term _ (VarExt (VarExt _))
              subst' sigmaBinding VarLast =
                Expr2 $ TermCons $ Pair (VarWkn . VarWkn <$> sigmaBinding) (Var2 $ VarWkn VarLast) (Var2 VarLast)
              subst' sigmaBinding (VarWkn v) = Var2 $ VarWkn $ VarWkn $ v
              subst :: Binding Type Term _ _ -> Type _ (VarExt _) -> Type _ (VarExt (VarExt _))
              subst sigmaBinding = swallow . fmap (subst' sigmaBinding)
          addNewConstraint
            (JudTermRel
              (Eta True)
              (VarWkn . VarWkn <$> deg)
              (gamma :.. VarFromCtx <$> segFst :.. VarFromCtx <$> segSnd)
              (Twice2
                (_namedBinding'body $ _namedBinding'body $ pairClause1)
                (_namedBinding'body $ _namedBinding'body $ pairClause2)
              )
              (Twice2
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
        (BoxType boxSeg1, BoxType boxSeg2) -> do
           let segContent :: Segment (Twice2 Type) _ _
               segContent = Declaration
                              (DeclNameSegment $ _namedBinding'name boxClause1)
                              (compModedModality dmu (_segment'modty boxSeg1))
                              Explicit
                              (Twice2
                                (_segment'content boxSeg1)
                                (_segment'content boxSeg2)
                              )
           let subst :: Segment Type _ _ -> VarExt _ -> Term _ (VarExt _)
               subst boxSeg VarLast = Expr2 $ TermCons $ ConsBox (VarWkn <$> boxSeg) $ Var2 VarLast
               subst boxSeg (VarWkn v) = Var2 $ VarWkn v
           addNewConstraint
             (JudTermRel
               (Eta True)
               (VarWkn <$> deg)
               (gamma :.. VarFromCtx <$> segContent)
               (Twice2
                 (_namedBinding'body $ boxClause1)
                 (_namedBinding'body $ boxClause2)
               )
               (Twice2
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
        let zero :: Term sys v
            zero = Expr2 $ TermCons $ ConsZero
        addNewConstraint
          (JudTermRel
            (Eta True)
            deg
            gamma
            (Twice2 clauseZero1 clauseZero2)
            (Twice2
              (substLast2 zero $ _namedBinding'body motive1)
              (substLast2 zero $ _namedBinding'body motive2)
            )
          )
          (Just parent)
          "Relating zero clauses."
        let nat = (Type $ Expr2 $ TermCons $ ConsUniHS $ NatType)
        let segPred :: Segment (Twice2 Type) _ _
            segPred = Declaration
                        (DeclNameSegment $ _namedBinding'name clauseSuc1)
                        dmu
                        Explicit
                        (Twice2 nat nat)
        let segHyp :: Segment (Twice2 Type) _ (VarExt _)
            segHyp = Declaration
                       (DeclNameSegment $ _namedBinding'name $ _namedBinding'body clauseSuc1)
                       (idModedModality $ VarWkn . unVarFromCtx <$> ctx'mode gamma)
                       Explicit
                       (Twice2
                         (_namedBinding'body motive1)
                         (_namedBinding'body motive2)
                       )
        let substS :: VarExt v -> Term sys (VarExt (VarExt v))
            substS VarLast = Expr2 $ TermCons $ ConsSuc $ Var2 $ VarWkn VarLast
            substS (VarWkn v) = Var2 $ VarWkn $ VarWkn v
        addNewConstraint
          (JudTermRel
            (Eta True)
            (VarWkn . VarWkn <$> deg)
            (gamma :.. VarFromCtx <$> segPred :.. VarFromCtx <$> segHyp)
            (Twice2
              (_namedBinding'body $ _namedBinding'body $ clauseSuc1)
              (_namedBinding'body $ _namedBinding'body $ clauseSuc2)
            )
            (Twice2
              (swallow $ substS <$> _namedBinding'body motive1)
              (swallow $ substS <$> _namedBinding'body motive2)
            )
          )
          (Just parent)
          "Relating successor clauses."
      (ElimNat _ _, _) -> tcFail parent "Terms are presumed to be well-typed in related types."
      --(_, _) -> _checkDependentEliminatorRelNoEta
      
checkEliminatorRelNoEta :: forall sys tc v .
  (SysTC sys, MonadTC sys tc, DeBruijnLevel v) =>
  Constraint sys ->
  Degree sys v ->
  Ctx (Twice2 Type) sys v Void ->
  ModedModality sys v ->
  Term sys v ->
  Term sys v ->
  UniHSConstructor sys v ->
  UniHSConstructor sys v ->
  Eliminator sys v ->
  Eliminator sys v ->
  UniHSConstructor sys v ->
  UniHSConstructor sys v ->
  tc ()
checkEliminatorRelNoEta parent deg gamma dmu
  eliminee1 eliminee2
  tyEliminee1 tyEliminee2
  eliminator1 eliminator2
  ty1 ty2 = case (eliminator1, eliminator2) of
  (App arg1, App arg2) -> case (tyEliminee1, tyEliminee2) of
    (Pi binding1, Pi binding2) -> do
      let dmu = _segment'modty $ binding'segment $ binding1
      let dom1 = _segment'content $ binding'segment binding1
      let dom2 = _segment'content $ binding'segment binding2
      addNewConstraint
        (JudTermRel
          (Eta True)
          (divDeg dmu deg)
          (VarFromCtx <$> dmu :\\ gamma)
          (Twice2 arg1 arg2)
          (Twice2 dom1 dom2)
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
  (Funext, Funext) -> return ()
  (Funext, _) -> tcFail parent "False."
  (ElimDep motive1 clauses1, ElimDep motive2 clauses2) -> do
    let seg = Declaration
          (DeclNameSegment $ _namedBinding'name motive1)
          dmu
          Explicit
          (Twice2 (hs2type tyEliminee1) (hs2type tyEliminee2))
    addNewConstraint
      (JudTypeRel
        (VarWkn <$> deg)
        (gamma :.. VarFromCtx <$> seg)
        (Twice2 (_namedBinding'body motive1) (_namedBinding'body motive2))
      )
      (Just parent)
      "Relating the motives."
    checkDependentEliminatorRelNoEta parent deg gamma dmu
      eliminee1 eliminee2
      tyEliminee1 tyEliminee2
      motive1 motive2
      clauses1 clauses2
      ty1 ty2
  (ElimDep _ _, _) -> tcFail parent "False."
  (ElimEq motive1 crefl1, ElimEq motive2 crefl2) -> case (tyEliminee1, tyEliminee2) of
    (EqType tyAmbient1 tL1 tR1, EqType tyAmbient2 tL2 tR2) -> do
      let bodyMotive1 = _namedBinding'body $ _namedBinding'body motive1
      let bodyMotive2 = _namedBinding'body $ _namedBinding'body motive2
      let segR = Declaration
               (DeclNameSegment $ _namedBinding'name motive1)
               dmu
               Explicit
               (Twice2 tyAmbient1 tyAmbient2)
      let segEq = Declaration
               (DeclNameSegment $ _namedBinding'name $ _namedBinding'body $ motive1)
               (VarWkn <$> dmu)
               Explicit
               (Twice2
                 (hs2type $ EqType (VarWkn <$> tyAmbient1) (VarWkn <$> tL1) (Var2 VarLast))
                 (hs2type $ EqType (VarWkn <$> tyAmbient2) (VarWkn <$> tL2) (Var2 VarLast))
               )
      addNewConstraint
        (JudTypeRel
          (VarWkn . VarWkn <$> deg)
          (gamma :.. VarFromCtx <$> segR :.. VarFromCtx <$> segEq)
          (Twice2 (_namedBinding'body $ _namedBinding'body motive1)
                 (_namedBinding'body $ _namedBinding'body motive2))
        )
        (Just parent)
        "Relating the motives"
      addNewConstraint
        (JudTermRel (Eta True) deg gamma (Twice2 crefl1 crefl2) $ Twice2
          (substLast2 tL1 $ substLast2 (Expr2 $ TermCons $ ConsRefl :: Term sys _) $ bodyMotive1)
          (substLast2 tL2 $ substLast2 (Expr2 $ TermCons $ ConsRefl :: Term sys _) $ bodyMotive2)
        )
        (Just parent)
        "Relating elimination clauses for the refl constructor."
    (_, _) -> unreachable
  (ElimEq _ _, _) -> tcFail parent "False."
  --(_, _) -> _checkEliminatorRelNoEta

checkTermRelWHNTermsNoEta :: (SysTC sys, MonadTC sys tc, DeBruijnLevel v) =>
  Constraint sys ->
  Degree sys v ->
  Ctx (Twice2 Type) sys v Void ->
  Term sys v ->
  Term sys v ->
  UniHSConstructor sys v ->
  UniHSConstructor sys v ->
  tc ()
checkTermRelWHNTermsNoEta parent deg gamma t1 t2 ty1 ty2 = case (t1, t2) of
  (Expr2 (TermCons c1), Expr2 (TermCons c2)) -> checkConstructorTermRelNoEta parent deg gamma c1 c2 ty1 ty2
  (Expr2 (TermSys syst1), _) -> checkTermRelSysTermWHNTermNoEta parent deg          gamma  syst1 t2 ty1 ty2
  (_, Expr2 (TermSys syst2)) -> checkTermRelSysTermWHNTermNoEta parent deg (flipCtx gamma) syst2 t1 ty2 ty1
  (Var2 v1, Var2 v2) -> if v1 == v2
          then return ()
          else tcFail parent "Cannot relate different variables."
  (Var2 v, _) -> tcFail parent "False."
  (Expr2 (TermElim dmu1 eliminee1 tyEliminee1 eliminator1), Expr2 (TermElim dmu2 eliminee2 tyEliminee2 eliminator2)) -> do
    let tyEliminee1' = hs2type $ tyEliminee1
    let tyEliminee2' = hs2type $ tyEliminee2
    addNewConstraint
      (JudModedModalityRel ModEq
        (crispModedModality :\\ gamma)
        dmu1 dmu2
        (unVarFromCtx <$> ctx'mode gamma)
      )
      (Just parent)
      "Relating modalities."
    addNewConstraint
      (JudTypeRel
        (divDeg dmu1 deg)
        (VarFromCtx <$> dmu1 :\\ gamma)
        (Twice2 tyEliminee1' tyEliminee2')
      )
      (Just parent)
      "Relating eliminees' types."
    addNewConstraint
      (JudTermRel
        (Eta False) -- lest you loop on `p = q : Nat >< Nat`
        (divDeg dmu1 deg)
        (VarFromCtx <$> dmu1 :\\ gamma)
        (Twice2 eliminee1 eliminee2)
        (Twice2 tyEliminee1' tyEliminee2')
      )
      (Just parent)
      "Relating eliminees."
    checkEliminatorRelNoEta parent deg gamma dmu1 eliminee1 eliminee2 tyEliminee1 tyEliminee2 eliminator1 eliminator2 ty1 ty2
  (Expr2 (TermElim _ _ _ _), _) -> tcFail parent "False."
  (Expr2 (TermMeta _ _ _ _), _) -> unreachable -- TODO consider neutrality
  (Expr2 (TermWildcard), _) -> unreachable
  (Expr2 (TermQName _ _), _) -> unreachable
  (Expr2 (TermAlgorithm _ _), _) -> unreachable
  (Expr2 (TermProblem t), _) -> tcFail parent "Nonsensical term."
  --(_, _) -> _checkTermNVRelNormal

tryToSolveTermNoEta :: (SysTC sys, MonadTC sys tc, DeBruijnLevel v) =>
  Constraint sys ->
  Degree sys v ->
  Ctx (Twice2 Type) sys v Void ->
  Term sys v ->
  Term sys v ->
  [Int] ->
  UniHSConstructor sys v ->
  UniHSConstructor sys v ->
  (String -> tc ()) ->
  tc ()
tryToSolveTermNoEta parent deg gamma t1 t2 metasT1 ty1 ty2 alternative = _

checkTermRelNoEta :: (SysTC sys, MonadTC sys tc, DeBruijnLevel v) =>
  Constraint sys ->
  Degree sys v ->
  Ctx (Twice2 Type) sys v Void ->
  Term sys v ->
  Term sys v ->
  [Int] ->
  [Int] ->
  UniHSConstructor sys v ->
  UniHSConstructor sys v ->
  tc ()
checkTermRelNoEta parent deg gamma t1 t2 metasT1 metasT2 ty1 ty2 = do
  case (isBlockedOrMeta t1 metasT1, isBlockedOrMeta t2 metasT2) of
    -- Both are whnormal
    (False, False) -> checkTermRelWHNTermsNoEta parent deg gamma t1 t2 ty1 ty2
    -- Only one is whnormal: whsolve or block
    (True , False) -> tryToSolveTermNoEta parent deg          gamma  t1 t2 metasT1 ty1 ty2 $ tcBlock parent
    (False, True ) -> tryToSolveTermNoEta parent deg (flipCtx gamma) t2 t1 metasT2 ty1 ty2 $ tcBlock parent
    -- Neither is whnormal: block
    (True , True ) -> tcBlock parent "Cannot solve relation: both sides are blocked on a meta-variable."

--------------------------------------------------------
-- MAYBE ETA --
--------------------------------------------------------

tryToSolveTermMaybeEta :: (SysTC sys, MonadTC sys tc, DeBruijnLevel v) =>
  Constraint sys ->
  Degree sys v ->
  Ctx (Twice2 Type) sys v Void ->
  Term sys v {-^ Blocked. -} ->
  Term sys v ->
  UniHSConstructor sys v ->
  UniHSConstructor sys v ->
  (String -> tc ()) ->
  tc ()
tryToSolveTermMaybeEta parent deg gamma t1 t2 ty1 ty2 callEtaExpandIfApplicable = _

etaExpandIfApplicable :: (SysTC sys, MonadTC sys tc, DeBruijnLevel v) =>
  Constraint sys ->
  Degree sys v ->
  Ctx (Twice2 Type) sys v Void ->
  Term sys v ->
  Term sys v ->
  [Int] ->
  [Int] ->
  UniHSConstructor sys v ->
  UniHSConstructor sys v ->
  tc ()
etaExpandIfApplicable parent deg gamma t1 t2 metasT1 metasT2 ty1 ty2 = do
  let dgamma = unVarFromCtx <$> ctx'mode gamma
  let giveUp = checkTermRelNoEta parent deg gamma t1 t2 metasT1 metasT2 ty1 ty2
  case (ty1, ty2) of
    -- Pi-types: eta-expand
    (Pi piBinding1, Pi piBinding2) ->  do
      let seg1 = binding'segment piBinding1
      let dom2 = _segment'content $ binding'segment piBinding2
      let seg = over decl'content (\ dom1 -> Twice2 dom1 dom2) seg1
      let app1 = Expr2 $ TermElim
            (idModedModality $ VarWkn . unVarFromCtx <$> ctx'mode gamma)
            (VarWkn <$> t1) (VarWkn <$> Pi piBinding1) (App $ Var2 VarLast)
      let app2 = Expr2 $ TermElim
            (idModedModality $ VarWkn . unVarFromCtx <$> ctx'mode gamma)
            (VarWkn <$> t2) (VarWkn <$> Pi piBinding2) (App $ Var2 VarLast)
      addNewConstraint
        (JudTermRel
          (Eta True)
          (VarWkn <$> deg)
          (gamma :.. VarFromCtx <$> seg)
          (Twice2 app1 app2)
          (Twice2
            (Type $ binding'body piBinding1)
            (Type $ binding'body piBinding2)
          )
        )
        (Just parent)
        "Eta: Relating function bodies."
    (Pi _, _) -> tcFail parent "Types are presumed to be related."
    (_, Pi _) -> tcFail parent "Types are presumed to be related."
    -- Sigma types: eta expand if allowed
    (Sigma sigmaBinding1, Sigma sigmaBinding2) -> do
      let dmu = _segment'modty $ binding'segment $ sigmaBinding1
      allowsEta dmu dgamma >>= \case
        Just True -> do
          let fst1 = Expr2 $ TermElim (modedApproxLeftAdjointProj dmu dgamma) t1 (Sigma sigmaBinding1) Fst
          let fst2 = Expr2 $ TermElim (modedApproxLeftAdjointProj dmu dgamma) t2 (Sigma sigmaBinding2) Fst
          let snd1 = Expr2 $ TermElim (idModedModality dgamma) t1 (Sigma sigmaBinding1) Snd
          let snd2 = Expr2 $ TermElim (idModedModality dgamma) t2 (Sigma sigmaBinding2) Snd
          addNewConstraint
            (JudTermRel
              (Eta True)
              (divDeg dmu deg)
              (VarFromCtx <$> dmu :\\ gamma)
              (Twice2 fst1 fst2)
              (Twice2
                (_segment'content $ binding'segment sigmaBinding1)
                (_segment'content $ binding'segment sigmaBinding2)
              )
            )
            (Just parent)
            "Eta: Relating first projections."
          addNewConstraint
            (JudTermRel
              (Eta True)
              deg
              gamma
              (Twice2 snd1 snd2)
              (Twice2
                (Type $ substLast2 fst1 $ binding'body sigmaBinding1)
                (Type $ substLast2 fst2 $ binding'body sigmaBinding2)
              )
            )
            (Just parent)
            "Eta: relating second projections"
        Just False -> giveUp
        Nothing -> tcBlock parent $ "Need to know if sigma-type has eta."
    (Sigma _, _) -> tcFail parent "Types are presumed to be related."
    (_, Sigma _) -> tcFail parent "Types are presumed to be related."
    -- Unit type: eta-expand
    (UnitType, UnitType) -> return ()
    (UnitType, _) -> tcFail parent "Types are presumed to be related."
    (_, UnitType) -> tcFail parent "Types are presumed to be related."
    -- Box type: eta-expand
    (BoxType boxSeg1, BoxType boxSeg2) -> do
      let dmu = _segment'modty $ boxSeg1
      allowsEta dmu dgamma >>= \case
        Just True -> do
          let unbox1 = Expr2 $ TermElim (modedApproxLeftAdjointProj dmu dgamma) t1 (BoxType boxSeg1) Unbox
          let unbox2 = Expr2 $ TermElim (modedApproxLeftAdjointProj dmu dgamma) t2 (BoxType boxSeg2) Unbox
          addNewConstraint
            (JudTermRel
              (Eta True)
              (divDeg dmu deg)
              (VarFromCtx <$> dmu :\\ gamma)
              (Twice2 unbox1 unbox2)
              (Twice2
                (_segment'content boxSeg1)
                (_segment'content boxSeg2)
              )
            )
            (Just parent)
            "Eta: Relating box contents."
        Just False -> giveUp
        Nothing -> tcBlock parent $ "Need to know if sigma-type has eta."
    (BoxType _, _) -> tcFail parent "Types are presumed to be related."
    (_, BoxType _) -> tcFail parent "Types are presumed to be related."
    (_, _) -> giveUp

checkTermRelMaybeEta :: (SysTC sys, MonadTC sys tc, DeBruijnLevel v) =>
  Constraint sys ->
  Degree sys v ->
  Ctx (Twice2 Type) sys v Void ->
  Term sys v ->
  Term sys v ->
  [Int] ->
  [Int] ->
  UniHSConstructor sys v ->
  UniHSConstructor sys v ->
  tc ()
checkTermRelMaybeEta parent deg gamma t1 t2 metasT1 metasT2 ty1 ty2 = do
  let callEtaExpandIfApplicable = etaExpandIfApplicable parent deg gamma t1 t2 metasT1 metasT2 ty1 ty2
  case (isBlockedOrMeta t1 metasT1, isBlockedOrMeta t2 metasT2) of
    (False, False) -> callEtaExpandIfApplicable
    (True , True ) -> callEtaExpandIfApplicable
    (True , False) -> tryToSolveTermMaybeEta parent deg          gamma  t1 t2 ty1 ty2 $ const callEtaExpandIfApplicable
    (False, True ) -> tryToSolveTermMaybeEta parent deg (flipCtx gamma) t2 t1 ty2 ty1 $ const callEtaExpandIfApplicable
    {-
    (True , False) -> case t1 of
      Expr2 (TermMeta neutrality meta (Compose depcies) alg) ->
        tryToSolveMetaMaybeEta parent deg          gamma  neutrality meta depcies t2 ty1 ty2
      _ -> callEtaExpandIfApplicable
    (False, True ) -> case t2 of
      Expr2 (TermMeta neutrality meta (Compose depcies) alg) ->
        tryToSolveMetaMaybeEta parent deg (flipCtx gamma) neutrality meta depcies t1 ty2 ty1
      _ -> callEtaExpandIfApplicable
    -}

--------------------------------------------------------

checkTermRel :: (SysTC sys, MonadTC sys tc, DeBruijnLevel v) =>
  Constraint sys ->
  Eta ->
  Degree sys v ->
  Ctx (Twice2 Type) sys v Void ->
  Term sys v ->
  Term sys v ->
  Type sys v ->
  Type sys v ->
  tc ()
checkTermRel parent eta deg gamma t1 t2 (Type ty1) (Type ty2) = do
  let dgamma = unVarFromCtx <$> ctx'mode gamma
  -- Top-relatedness is always ok.
  isTopDeg dgamma deg >>= \ case
    -- It's certainly about top-relatedness
    Just True -> return ()
    -- We don't know
    Nothing -> tcBlock parent $ "Need to know whether required degree of relatedness is Top."
    -- It's certainly not about top-relatedness
    Just False -> do
      -- purposefully shadowing (redefining)
      (t1, metasT1) <- runWriterT $ whnormalize parent (fstCtx gamma) t1 "Weak-head-normalizing first term."
      (t2, metasT2) <- runWriterT $ whnormalize parent (sndCtx gamma) t2 "Weak-head-normalizing second term."
      (ty1, metasTy1) <- runWriterT $ whnormalize parent (fstCtx gamma) ty1 "Weak-head-normalizing first type."
      (ty2, metasTy2) <- runWriterT $ whnormalize parent (sndCtx gamma) ty2 "Weak-head-normalizing second type."
      parent <- defConstraint
            (JudTermRel
              eta
              deg
              gamma
              (Twice2 t1 t2)
              (Twice2 (Type ty1) (Type ty2))
            )
            (Just parent)
            "Weak-head-normalize everything"

      case (ty1, ty2) of
        (Expr2 (TermCons (ConsUniHS tycode1)), Expr2 (TermCons (ConsUniHS tycode2))) ->
          if unEta eta
          then checkTermRelMaybeEta parent deg gamma t1 t2 metasT1 metasT2 tycode1 tycode2
          else checkTermRelNoEta parent deg gamma t1 t2 metasT1 metasT2 tycode1 tycode2
        (_, _) -> tcBlock parent $ "Need to weak-head-normalize types to tell whether I should use eta-expansion."

checkTypeRel :: (SysTC sys, MonadTC sys tc, DeBruijnLevel v) =>
  Constraint sys ->
  Degree sys v ->
  Ctx (Twice2 Type) sys v Void ->
  Type sys v ->
  Type sys v ->
  tc ()
checkTypeRel parent deg gamma (Type ty1) (Type ty2) =
  let uni = hs2type $ UniHS (unVarFromCtx <$> ctx'mode gamma) --(Expr2 $ TermWildcard)
  in  addNewConstraint
        (JudTermRel
          (Eta True)
          deg
          gamma
          (Twice2 ty1 ty2)
          (Twice2 uni uni)
        )
        (Just parent)
        "Checking relatedness of types in a Hofmann-Streicher universe."
