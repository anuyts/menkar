module Menkar.TC.ASTSolve where

import Menkar.System
import Menkar.Analyzer
import Menkar.Fine.Syntax
import Menkar.Basic.Context
import Menkar.Fine.Context
import Menkar.Fine.Judgement
import Menkar.Fine.LookupQName
import qualified Menkar.Raw.Syntax as Raw
import Menkar.Monad.Monad
import Menkar.WHN

import Control.Exception.AssertFalse
import Data.Constraint.Conditional

import Data.Void
import Control.Lens
import Data.Functor.Compose
import Control.Monad
import Control.Monad.Writer.Lazy
import Data.List
import Data.List.Unique
import Data.Proxy
import Data.Maybe
import Control.Monad.Trans.Maybe
import GHC.Generics
import Control.Applicative

---------------------------------------------------

-- | Immediately calls the analyzer.
newRelatedAST' :: forall sys tc t v vOrig .
  (SysTC sys, MonadTC sys tc, DeBruijnLevel v, DeBruijnLevel vOrig, Analyzable sys t) =>
  Constraint sys ->
  Relation t v ->
  Ctx Type sys vOrig Void ->
  Ctx (Twice2 Type) sys v Void ->
  (vOrig -> v) ->
  (v -> Maybe vOrig) ->
  t v ->
  ClassifExtraInput t vOrig ->
  ClassifExtraInput t v ->
  ClassifInfo (Twice1 (Classif t) v) ->
  tc (t vOrig)
newRelatedAST' parent relT gammaOrig gamma subst partialInv t2 extraT1orig extraT2 maybeCTs = do
  let maybeCT1 :: ClassifInfo (Classif t v) = fstTwice1 <$> maybeCTs
  let maybeCT2 :: ClassifInfo (Classif t v) = sndTwice1 <$> maybeCTs
  --let inputT1 :: Classification t v = (Classification _  extraT1 maybeCT1)
  let inputT2 :: Classification t v = (Classification t2 extraT2 maybeCT2)
  attempt <- sequenceA $ analyze TokenTrav gammaOrig inputT2
    $ \ wkn condT1origDraft extract extCtx extractRel addressInfo -> do
      let t1origDraft = runConditional condT1origDraft
      let inputT1orig :: Classification t vOrig = Classification t1origDraft extraT1orig ClassifUnknown
      let inputT1 :: Classification t v = subst <$> inputT1orig
      let Classification _  extraS1orig maybeCS1orig = fromMaybe unreachable $ extract gammaOrig inputT1orig
      let Classification s2 extraS2     maybeCS2 = fromMaybe unreachable $ extract (sndCtx gamma) inputT2
      let relS = extractRel relT
      let gammadeltaOrig = fromMaybe unreachable $ extCtx TokenFalse gammaOrig inputT1orig typesArentDoubled
      let gammadelta     = fromMaybe unreachable $ extCtx TokenTrue  gamma     inputT1     (conditional inputT2)
      let eta = case _addressInfo'focus addressInfo of
            FocusEliminee -> Eta False
            FocusWrapped -> Eta True
            NoFocus -> Eta True
      let substDelta = over traverse $ subst
      let partialInvDelta = traverse $ partialInv
      AnalysisTrav <$>
        newRelatedAST parent eta relS gammadeltaOrig gammadelta substDelta partialInvDelta s2 extraS1orig extraS2
        (classifMust2will $ Twice1 <$> (fmap substDelta <$> maybeCS1orig) <*> maybeCS2) (_addressInfo'reason addressInfo)
      -- Do something with the reason.
      {-case _addressInfo'boredom addressInfo of
        EntirelyBoring ->
          
            
        WorthMentioning -> _
        WorthScheduling -> do
          addNewConstraint
            (JudRel analyzableToken gamma)-}
  case attempt of
    Right (AnalysisTrav t1orig) -> return t1orig
    Left anErr -> case (anErr, analyzableToken :: AnalyzableToken sys t, t2) of
         (AnErrorTermMeta, AnTokenTermNV, TermMeta neutrality meta (Compose depcies) alg) ->
           unreachable -- terms are neutral at this point
         (AnErrorTermMeta, _, _) -> unreachable
         (AnErrorTermWildcard, AnTokenTermNV, TermWildcard) -> unreachable
         (AnErrorTermWildcard, _, _) -> unreachable
         (AnErrorTermQName, AnTokenTermNV, TermQName qname ldivVal) ->
           unreachable -- terms are neutral at this point
         (AnErrorTermQName, _, _) -> unreachable
         (AnErrorTermAlreadyChecked, AnTokenTermNV, TermAlreadyChecked tChecked tyChecked) ->
           unreachable -- terms are neutral at this point
         (AnErrorTermAlreadyChecked, _, _) -> unreachable
         (AnErrorTermAlgorithm, AnTokenTermNV, TermAlgorithm alg tResult) -> 
           unreachable -- terms are neutral at this point
         (AnErrorTermAlgorithm, _, _) -> unreachable
         --(AnErrorTermSys sysErr, AnTokenTermNV, TermSys syst) ->
         --  TermSys <$> newRelatedUnanalyzableSysTerm sysErr parent relT gammaOrig gamma subst partialInv syst maybeCTs
         --(AnErrorTermSys _, _, _) -> unreachable
         (AnErrorTermProblem, AnTokenTermNV, TermProblem tProblem) -> tcFail parent "Problematic term encountered."
         (AnErrorTermProblem, _, _) -> unreachable
         (AnErrorVar, AnTokenTerm, Var2 v2) -> case partialInv v2 of
           Just v1orig -> return $ Var2 v1orig
           Nothing ->
             tcFail parent "Have to resolve meta not depending on certain variable, with solution that does depend on it."
         (AnErrorVar, _, _) -> unreachable
         (AnErrorSys sysError, _, _) -> newRelatedSysASTUnanalyzable' sysError
           parent relT gammaOrig gamma subst partialInv t2 extraT1orig extraT2 maybeCTs

-- | To be called by the analyzer.
newRelatedAST :: forall sys tc t v vOrig .
  (SysTC sys, MonadTC sys tc, DeBruijnLevel v, DeBruijnLevel vOrig, Analyzable sys t) =>
  Constraint sys ->
  Eta ->
  Relation t v ->
  Ctx Type sys vOrig Void ->
  Ctx (Twice2 Type) sys v Void ->
  (vOrig -> v) ->
  (v -> Maybe vOrig) ->
  t v ->
  ClassifExtraInput t vOrig ->
  ClassifExtraInput t v ->
  ClassifInfo (Twice1 (Classif t) v) ->
  String ->
  tc (t vOrig)
newRelatedAST parent eta relT gammaOrig gamma subst partialInv t2 extraT1orig extraT2 maybeCTs reason =
  case analyzableToken @sys @t of
    AnTokenTerm ->
      newRelatedMetaTerm parent eta relT gammaOrig gamma subst partialInv t2 maybeCTs
        (if unEta eta then MetaBlocked else MetaNeutral) reason
    AnTokenSys sysToken ->
      newRelatedSysAST sysToken parent eta relT gammaOrig gamma subst partialInv t2 extraT1orig extraT2 maybeCTs reason
    _ -> newRelatedAST' parent relT gammaOrig gamma subst partialInv t2 extraT1orig extraT2 maybeCTs

newRelatedMetaTerm :: forall sys tc v vOrig .
  (SysTC sys, MonadTC sys tc, Eq v, DeBruijnLevel v, DeBruijnLevel vOrig) =>
  Constraint sys ->
  Eta ->
  ModedDegree sys v ->
  Ctx Type sys vOrig Void ->
  Ctx (Twice2 Type) sys v Void ->
  (vOrig -> v) ->
  (v -> Maybe vOrig) ->
  Term sys v ->
  ClassifInfo (Twice1 (Type sys) v) ->
  MetaNeutrality ->
  String ->
  tc (Term sys vOrig)
newRelatedMetaTerm parent eta deg gammaOrig gamma subst partialInv t2 maybeTys neutrality reason = do
      t1orig <- newMetaTermNoCheck (Just parent) gammaOrig neutrality Nothing reason
      let t1 = subst <$> t1orig
      addNewConstraint
        (JudRel AnTokenTerm eta deg gamma (Twice1 t1 t2) (Twice1 U1 U1) maybeTys)
        (Just parent)
        reason
      return t1orig

--------------------------------------------------------
-- NO ETA --
--------------------------------------------------------

solveMetaAgainstWHNF :: forall sys tc v vOrig .
  (SysTC sys, MonadTC sys tc, Eq v, DeBruijnLevel v, DeBruijnLevel vOrig) =>
  Constraint sys ->
  ModedDegree sys v ->
  Ctx Type sys vOrig Void ->
  Ctx (Twice2 Type) sys v Void ->
  (vOrig -> v) ->
  (v -> Maybe vOrig) ->
  Term sys v ->
  Type sys v ->
  Type sys v ->
  [Int] ->
  [Int] ->
  tc (Term sys vOrig)
solveMetaAgainstWHNF parent deg gammaOrig gamma subst partialInv t2 ty1 ty2 metasTy1 metasTy2 =
  newRelatedAST' parent deg gammaOrig gamma subst partialInv t2 U1 U1 (ClassifWillBe $ Twice1 ty1 ty2)
    {-("Inferring the solution - which is pointless since we would be solving a meta with a meta."
     ++ " So if I'm doing this, that is probably a bug.")-}

{-| Precondition: @partialInv . subst = Just@.
-}
solveMetaImmediately :: (SysTC sys, MonadTC sys tc, Eq v, DeBruijnLevel v, DeBruijnLevel vOrig) =>
  Constraint sys ->
  Ctx Type sys vOrig Void ->
  Ctx (Twice2 Type) sys v Void ->
  (vOrig -> v) ->
  (v -> Maybe vOrig) ->
  Term sys v ->
  Term sys v ->
  Type sys v ->
  Type sys v ->
  [Int] ->
  [Int] ->
  tc (Term sys vOrig)
solveMetaImmediately parent gammaOrig gamma subst partialInv t2 nonwhnt2 ty1 ty2 metasTy1 metasTy2 = do
  -- Try to write t2 in gammaOrig
  let dgamma' = ctx'mode gamma
      dgamma = unVarFromCtx <$> dgamma'
  let maybeT2orig = (sequenceA $ partialInv <$> nonwhnt2) <|> (sequenceA $ partialInv <$> t2)
  case maybeT2orig of
    -- If it works, return that.
    Just t2orig -> case (sequenceA $ partialInv <$> ty1) of
      Nothing -> return $ t2orig
      Just ty1orig -> return $ Expr2 $ TermAlreadyChecked t2orig ty1orig
    -- If t2 contains variables not in gammaOrig: solve against WHNF
    Nothing ->
      solveMetaAgainstWHNF parent (modedEqDeg dgamma) gammaOrig gamma subst partialInv t2 ty1 ty2 metasTy1 metasTy2

--------------------------------------------------------
-- ALWAYS ETA --
--------------------------------------------------------

{-| Returns an eta-expansion if eta is certainly allowed, @Just Nothing@ if it's not allowed, and @Nothing@ if unclear.
-}
etaExpand ::
  (SysTC sys, MonadTC sys tc, DeBruijnLevel v) =>
  Constraint sys ->
  Ctx Type sys v Void ->
  Term sys v ->
  UniHSConstructor sys v ->
  tc (Maybe (Maybe (Term sys v)))
etaExpand parent gamma t (Pi piBinding) = do
  body <- newMetaTerm
            (Just parent)
            --(eqDeg :: Degree sys _)
            (gamma :.. (VarFromCtx <$> binding'segment piBinding))
            (binding'body piBinding)
            MetaBlocked
            "Infer function body."
  return $ Just $ Just $ Expr2 $ TermCons $ Lam $ Binding (binding'segment piBinding) (ValRHS body $ binding'body piBinding)
etaExpand parent gamma t (Sigma sigmaBinding) = do
  let dgamma' = ctx'mode gamma
  let dgamma = unVarFromCtx <$> dgamma'
  let dmu = _segment'modty $ binding'segment $ sigmaBinding
  allowsEta parent (crispModedModality dgamma' :\\ gamma) dmu "Need to know if eta is allowed." >>= \case
    Just True -> do
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
                   (substLast2 tmFst $ binding'body sigmaBinding)
                   MetaBlocked
                   "Infer second projection."
        return $ Just $ Just $ Expr2 $ TermCons $ Pair sigmaBinding tmFst tmSnd
    Just False -> return $ Just Nothing
    Nothing -> return $ Nothing
etaExpand parent gamma t (BoxType boxSeg) = do
  let dgamma' = ctx'mode gamma
  let dgamma = unVarFromCtx <$> dgamma'
  let dmu = _segment'modty $ boxSeg
  allowsEta parent (crispModedModality dgamma' :\\ gamma) dmu "Need to know if eta is allowed." >>= \case
    Just True -> do
      let ty = Type $ Expr2 $ TermCons $ ConsUniHS $ BoxType boxSeg
      tmUnbox <- newMetaTerm
                   (Just parent)
                   --(eqDeg :: Degree sys _)
                   (VarFromCtx <$> dmu :\\ gamma)
                   (_segment'content boxSeg)
                   MetaBlocked
                   "Infer box content."
      return $ Just $ Just $ Expr2 $ TermCons $ ConsBox boxSeg tmUnbox
    Just False -> return $ Just Nothing
    Nothing -> return $ Nothing
etaExpand parent gamma t UnitType = return $ Just $ Just $ Expr2 $ TermCons $ ConsUnit
etaExpand parent gamma t (UniHS _) = return $ Just $ Nothing
etaExpand parent gamma t EmptyType = return $ Just $ Nothing
etaExpand parent gamma t NatType = return $ Just $ Nothing
etaExpand parent gamma t (EqType _ _ _) = return $ Just $ Nothing
etaExpand parent gamma t (SysType sysType) = etaExpandSysType parent gamma t sysType

checkEtaForNormalType :: forall sys tc v .
  (SysTC sys, MonadTC sys tc, DeBruijnLevel v) =>
  Constraint sys ->
  Ctx Type sys v Void ->
  Term sys v ->
  UniHSConstructor sys v ->
  tc Bool
checkEtaForNormalType parent gamma t ty = do
  maybeMaybeTExpanded <- etaExpand parent gamma t ty
  let ty' = hs2type ty
  case maybeMaybeTExpanded of
    Nothing -> tcBlock parent $ "Need to know if this type has eta."
    Just Nothing -> return False
    Just (Just tExpanded) -> do
      addNewConstraint
        (JudTermRel
          (Eta True)
          (modedEqDeg $ unVarFromCtx <$> ctx'mode gamma)
          (duplicateCtx gamma)
          (Twice2 t tExpanded)
          (Twice2 ty' ty')
        )
        (Just parent)
        "Eta-expand"
      return True

-- | Check whether a term is equal to its eta expansion if that exists.
checkEta ::
  (SysTC sys, MonadTC sys tc, DeBruijnLevel v) =>
  Constraint sys ->
  Ctx Type sys v Void ->
  Term sys v ->
  Type sys v ->
  tc Bool
checkEta parent gamma t ty = do
  (whnTy, metas) <- runWriterT $ whnormalizeType parent gamma ty "Normalizing type."
  case metas of
    [] -> do
      parent' <- defConstraint
                   (JudEta gamma t whnTy)
                   (Just parent)
                   "Weak-head-normalized type."
      case unType whnTy of
        Var2 v -> return False
        Expr2 whnTyNV -> case whnTyNV of
          TermCons (ConsUniHS whnTyCons) -> checkEtaForNormalType parent' gamma t whnTyCons
          TermCons _ -> tcFail parent' $ "Type is not a type."
          TermElim _ _ _ _ -> return False
          TermMeta MetaBlocked _ _ _ -> unreachable
          TermMeta MetaNeutral _ _ _ -> tcBlock parent "Need to weak-head-normalize type before I can eta-expand."
          TermWildcard -> unreachable
          TermQName _ _ -> unreachable
          TermAlreadyChecked _ _ -> unreachable
          TermAlgorithm _ _ -> unreachable
          TermSys whnSysTy -> checkEtaWHNSysTy parent' gamma t whnSysTy
          TermProblem _ -> tcFail parent' $ "Nonsensical type."
    _ -> tcBlock parent "Need to weak-head-normalize type before I can eta-expand."

--------------------------------------------------------
-- MAYBE ETA IF SPECIFIED --
--------------------------------------------------------


tryToSolveMeta :: forall sys tc v .
  (SysTC sys, MonadTC sys tc, DeBruijnLevel v) =>
  Constraint sys ->
  Eta ->
  ModedDegree sys v ->
  Ctx (Twice2 Type) sys v Void ->
  MetaNeutrality -> Int -> [Term sys v] -> Maybe (Algorithm sys v) ->
  Term sys v ->
  Term sys v ->
  Type sys v ->
  Type sys v ->
  [Int] ->
  [Int] ->
  (String -> tc ()) {-^ Either block or resort to eta-equality. -} ->
  tc ()
tryToSolveMeta parent eta deg gamma neutrality1 meta1 depcies1 maybeAlg1 t2 nonwhnt2 ty1 ty2 metasTy1 metasTy2
  alternative = do
  let getVar2 :: Term sys v -> Maybe v
      getVar2 (Var2 v) = Just v
      getVar2 _ = Nothing
  let dgamma' = ctx'mode gamma
  let dgamma = unVarFromCtx <$> dgamma'
  case sequenceA $ getVar2 <$> depcies1 of
    -- Some dependency is not a variable
    Nothing -> alternative "Cannot solve meta-variable: it has non-variable dependencies."
    -- All dependencies are variables
    Just depcyVars -> do
      let (_, repeatedVars, _) = complex depcyVars
      case repeatedVars of
        -- Some variables occur twice
        _:_ -> alternative "Cannot solve meta-variable: it has undergone contraction of dependencies."
        -- All variables are unique
        [] -> solveMeta parent meta1 ( \ gammaOrig -> do
            -- Turn list of variables into a function mapping variables from gammaOrig to variables from gamma
            let subst = (depcyVars !!) . fromIntegral . (getDeBruijnLevel Proxy)
            let partialInv = join . fmap (forDeBruijnLevel Proxy . fromIntegral) . flip elemIndex depcyVars
            itIsEqDeg <- isEqDeg parent (crispModedModality dgamma' :\\ fstCtx gamma) (_degree'deg deg) dgamma
              "Need to know if I'm checking for equality"
            -- If we're checking equality, we can take a shortcut.
            solution <- case itIsEqDeg of
              -- We're certainly checking equality: solve the meta immediately.
              Just True ->
                Just <$> solveMetaImmediately parent gammaOrig gamma subst partialInv t2 nonwhnt2 ty1 ty2 metasTy1 metasTy2
              -- We may not be checking equality.
              _ -> -- Check if eta is allowed.
                   if unEta eta
                   then do --Nothing <$ alternative "Let's try eta-expansion."
                     -- t1 is the meta-term
                     let t1 = Expr2 $ TermMeta neutrality1 meta1 (Compose depcies1) (Compose maybeAlg1)
                     -- If the type has eta, this statement equates the meta t1 to its eta-expansion and returns True.
                     -- Otherwise, it does nothing and returns false.
                     etaHolds <- checkEta parent (fstCtx gamma) t1 ty1
                     -- Check if the type has eta.
                     if etaHolds
                       -- If so, then above we have equated the meta to its expansion, so we can just come back later on.
                       then Nothing <$ addConstraint parent
                       -- Otherwise, solve against the WHNF.
                       else Just <$> solveMetaAgainstWHNF parent deg
                          gammaOrig gamma subst partialInv t2 ty1 ty2 metasTy1 metasTy2
                   -- Otherwise, solve against the WHNF.
                   else Just <$> solveMetaAgainstWHNF parent deg
                          gammaOrig gamma subst partialInv t2 ty1 ty2 metasTy1 metasTy2
            case neutrality1 of
              MetaBlocked -> return solution
              MetaNeutral -> case solution of
                Just (Expr2 (TermCons c)) -> tcFail parent $
                  "Cannot instantiate neutral meta with a constructor. " ++
                  "(If the expected solution is an eta-expanded normal expression, then we've found a bug.)"
                  -- In the future (e.g. when you do neutral-implicit annotations), you may want to try and eta-contract c.
                  -- Note that `x > (f x .1 , f x ..2)` is not easy to eta-contract to `f`.
                  -- Best done using an eta-contraction judgement analogous to smart-elim judgement.
                _ -> return solution
          )
  
tryToSolveTerm :: forall sys tc v .
  (SysTC sys, MonadTC sys tc, DeBruijnLevel v) =>
  Constraint sys ->
  Eta ->
  ModedDegree sys v ->
  Ctx (Twice2 Type) sys v Void ->
  Term sys v {-^ Blocked. -} ->
  Term sys v ->
  Term sys v ->
  Type sys v ->
  Type sys v ->
  [Int] ->
  [Int] ->
  (String -> tc ()) ->
  tc ()
tryToSolveTerm parent eta deg gamma t1 t2 nonwhnt2 ty1 ty2 metasTy1 metasTy2 alternative = case t1 of
  (Expr2 (TermMeta neutrality1 meta1 (Compose depcies1) (Compose maybeAlg1))) ->
    tryToSolveMeta parent eta deg gamma neutrality1 meta1 depcies1 maybeAlg1 t2 nonwhnt2 ty1 ty2 metasTy1 metasTy2 alternative
  _ -> alternative "Cannot solve relation: one side is blocked on a meta-variable."
