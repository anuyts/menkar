module Menkar.TC.ASTRel where

import Menkar.Fine
import Menkar.Analyzer
import Menkar.WHN
import Menkar.System.TC
import Menkar.Basic.Context
import Menkar.Monad

import Control.Exception.AssertFalse

import Data.Void
import Control.Lens
import Data.Functor.Compose
import Control.Monad
import Control.Monad.Writer.Lazy

---------------------------------------------------

{-
checkASTRel :: (SysTC sys, MonadTC sys tc, DeBruijnLevel v, Analyzable sys t) =>
  Constraint sys ->
  Eta ->
  Relation t v ->
  Ctx (Twice2 Type) sys v Void ->
  Twice1 t v ->
  AnalyzerExtraInput t v ->
  ClassifInfo (Twice1 (Classif t) v) ->
  tc ()
checkASTRel parent eta relT gamma (Twice1 t t') extraT maybeCTs = do
  let maybeCT  = fstTwice1 <$> maybeCTs
  let maybeCT' = sndTwice1 <$> maybeCTs
  attempt <- sequenceA $ analyze TokenRelate (\x -> Twice2 x x) gamma
    (AnalyzerInput t extraT maybeCT (IfRelate relT))
    $ \ wkn gammadelta (AnalyzerInput s extraS maybeCS (IfRelate relS)) addressInfo extract ->
      _
  _
-}

---------------------------------------------------

checkTermRelNoEta :: (SysTC sys, MonadTC sys tc, DeBruijnLevel v) =>
  Constraint sys ->
  ModedDegree sys v ->
  Ctx (Twice2 Type) sys v Void ->
  Term sys v ->
  Term sys v ->
  [Int] ->
  [Int] ->
  Type sys v ->
  Type sys v ->
  [Int] ->
  [Int] ->
  tc ()
checkTermRelNoEta parent deg gamma t1 t2 metasT1 metasT2 ty1 ty2 metasTy1 metasTy2 = _checkTermRelNoEta

---------------------------------------------------

etaExpandIfApplicable :: (SysTC sys, MonadTC sys tc, DeBruijnLevel v) =>
  Constraint sys ->
  ModedDegree sys v ->
  Ctx (Twice2 Type) sys v Void ->
  Term sys v ->
  Term sys v ->
  [Int] ->
  [Int] ->
  UniHSConstructor sys v ->
  UniHSConstructor sys v ->
  tc ()
etaExpandIfApplicable parent ddeg gamma t1 t2 metasT1 metasT2 ty1 ty2 = do
  let dgamma' = ctx'mode gamma
  let dgamma = unVarFromCtx <$> dgamma'
  let giveUp = checkTermRelNoEta parent ddeg gamma t1 t2 metasT1 metasT2 (hs2type ty1) (hs2type ty2) [] []
  maybeExpansions <- case (ty1, ty2) of
    -- Pi-types: eta-expand
    (Pi piBinding1, Pi piBinding2) -> do
      let app1 = Expr2 $ TermElim
            (idModedModality $ VarWkn <$> dgamma)
            (VarWkn <$> t1) (VarWkn <$> Pi piBinding1) (App $ Var2 VarLast)
      let app2 = Expr2 $ TermElim
            (idModedModality $ VarWkn <$> dgamma)
            (VarWkn <$> t2) (VarWkn <$> Pi piBinding2) (App $ Var2 VarLast)
      return $ Just (Expr2 $ TermCons $ Lam $ Binding (binding'segment piBinding1) app1,
                     Expr2 $ TermCons $ Lam $ Binding (binding'segment piBinding2) app2)
    (Pi _, _) -> tcFail parent "Types are presumed to be related."
    (_, Pi _) -> tcFail parent "Types are presumed to be related."
    (_, _) -> Nothing <$ giveUp
  case maybeExpansions of
    Just (expandT1, expandT2) ->
      addNewConstraint
        (JudTermRel
          (Eta False)
          ddeg
          gamma
          (Twice2 expandT1 expandT2)
          (Twice2 (hs2type ty1) (hs2type ty2))
        )
        (Just parent)
        "Eta-expand."
    Nothing -> return ()

  {-
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
          (VarWkn <$> (_degree'deg deg))
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
      etaAllowed <- allowsEta parent (crispModedModality dgamma' :\\ fstCtx gamma) dmu dgamma
        "Need to know if eta is allowed."
      case etaAllowed of
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
              (_degree'deg deg)
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
      etaAllowed <- allowsEta parent (crispModedModality dgamma' :\\ fstCtx gamma) dmu dgamma
        "Need to know if eta is allowed."
      case etaAllowed of
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
-}

checkTermRelMaybeEta :: (SysTC sys, MonadTC sys tc, DeBruijnLevel v) =>
  Constraint sys ->
  ModedDegree sys v ->
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
    (True , False) ->
      _tryToSolveTerm parent (Eta True) deg          gamma  t1 t2 (hs2type ty1) (hs2type ty2) [] []
      $ const callEtaExpandIfApplicable
    (False, True ) ->
      _tryToSolveTerm parent (Eta True) deg (flipCtx gamma) t2 t1 (hs2type ty2) (hs2type ty1) [] []
      $ const callEtaExpandIfApplicable
    (True , True ) -> tcBlock parent "Cannot solve relation: both sides are blocked on a meta-variable."
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

---------------------------------------------------

checkTermRel :: forall sys tc v .
  (SysTC sys, MonadTC sys tc, DeBruijnLevel v) =>
  Constraint sys ->
  Eta ->
  ModedDegree sys v ->
  Ctx (Twice2 Type) sys v Void ->
  Twice1 (Term sys) v ->
  ClassifInfo (Twice1 (Type sys) v) ->
  tc ()
checkTermRel parent eta ddeg gamma (Twice1 t1 t2) maybeTys = do
  let Twice1 ty1 ty2 = fromClassifInfo unreachable maybeTys
  let dgamma' = ctx'mode gamma
  let dgamma = unVarFromCtx <$> dgamma'
  -- Top-relatedness is always ok.
  itIsTopDeg <- isTopDeg parent (crispModedModality dgamma' :\\ fstCtx gamma) (_degree'deg ddeg) dgamma
    "Need to know whether required ddegree of relatedness is Top."
  case itIsTopDeg of
    -- It's certainly about top-relatedness
    Just True -> return ()
    -- We don't know
    Nothing -> tcBlock parent $ "Need to know whether required ddegree of relatedness is Top."
    -- It's certainly not about top-relatedness
    Just False -> do
      -- purposefully shadowing (redefining)
      (ty1, metasTy1) <- runWriterT $ whnormalizeType parent (fstCtx gamma) ty1 "Weak-head-normalizing first type."
      (ty2, metasTy2) <- runWriterT $ whnormalizeType parent (sndCtx gamma) ty2 "Weak-head-normalizing second type."
      (t1, metasT1) <- runWriterT $ whnormalize parent (fstCtx gamma) t1 ty1 "Weak-head-normalizing first term."
      (t2, metasT2) <- runWriterT $ whnormalize parent (sndCtx gamma) t2 ty2 "Weak-head-normalizing second term."
      parent <- defConstraint
            (JudTermRel
              eta
              ddeg
              gamma
              (Twice2 t1 t2)
              (Twice2 ty1 ty2)
            )
            (Just parent)
            "Weak-head-normalize everything"

      if unEta eta
        then case (unType ty1, unType ty2) of
               (Expr2 (TermCons (ConsUniHS tycode1)), Expr2 (TermCons (ConsUniHS tycode2))) ->
                 checkTermRelMaybeEta parent ddeg gamma t1 t2 metasT1 metasT2 tycode1 tycode2
               (_, _) -> case (isBlockedOrMeta (unType ty1) metasTy1, isBlockedOrMeta (unType ty2) metasTy2) of
                 (False, False) -> checkTermRelNoEta parent ddeg gamma t1 t2 metasT1 metasT2 ty1 ty2 [] []
                 (_    , _    ) ->
                   tcBlock parent $ "Need to weak-head-normalize types to tell whether I should use eta-expansion."
        else checkTermRelNoEta parent ddeg gamma t1 t2 metasT1 metasT2 ty1 ty2 [] []
