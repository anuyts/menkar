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
import Data.Functor.Functor1
import Data.Constraint.Witness
import Data.Functor.Coyoneda.NF
import Data.Functor.Coerce
import Control.DeepSeq.Redone

import Data.Void
import Control.Lens
import Data.Functor.Compose
import Control.Monad
import Control.Monad.Writer.Strict
import Data.List
import Data.List.Unique
import Data.Maybe
import Control.Monad.Trans.Maybe
import Control.Monad.Trans.Writer.Strict
import GHC.Generics
import Control.Applicative

---------------------------------------------------

-- | Immediately calls the analyzer.
newRelatedAST' :: forall sys tc t v vOrig .
  (SysTC sys, MonadTC sys tc, DeBruijnLevel v, DeBruijnLevel vOrig, Analyzable sys t) =>
  Coyoneda (Relation t) v ->
  Ctx Type sys vOrig ->
  Ctx (Twice2 Type) sys v ->
  (vOrig -> v) ->
  (v -> Maybe vOrig) ->
  t v ->
  ClassifExtraInput t vOrig ->
  ClassifExtraInput t v ->
  ClassifInfo (Twice1 (Classif t) v) ->
  tc (t vOrig)
newRelatedAST' relT gammaOrig gamma subst partialInv t2 extraT1orig extraT2 maybeCTs = do
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
      let relS = extractRel (ctx'mode gamma) relT
      let gammadeltaOrig = fromMaybe unreachable $ extCtx TokenFalse gammaOrig inputT1orig typesArentDoubled
      let gammadelta     = fromMaybe unreachable $ extCtx TokenTrue  gamma     inputT1     (conditional inputT2)
      let eta = case _addressInfo'focus addressInfo of
            FocusEliminee -> Eta False
            FocusWrapped -> Eta True
            NoFocus -> Eta True
      let substDelta = over traverse $ subst
      let partialInvDelta = traverse $ partialInv
      AnalysisTrav <$>
        newRelatedAST eta relS gammadeltaOrig gammadelta substDelta partialInvDelta s2 extraS1orig extraS2
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
         (AnErrorTermMeta, AnTokenTermNV, TermMeta neutrality meta depcies alg) ->
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
         (AnErrorTermProblem, AnTokenTermNV, TermProblem tProblem) -> tcFail "Problematic term encountered."
         (AnErrorTermProblem, _, _) -> unreachable
         (AnErrorVar, AnTokenTerm, Var2 v2) -> case partialInv v2 of
           Just v1orig -> return $ Var2 v1orig
           Nothing ->
             tcFail "Have to resolve meta not depending on certain variable, with solution that does depend on it."
         (AnErrorVar, _, _) -> unreachable
         (AnErrorSys sysError, _, _) -> newRelatedSysASTUnanalyzable' sysError
           relT gammaOrig gamma subst partialInv t2 extraT1orig extraT2 maybeCTs

-- | To be called by the analyzer.
newRelatedAST :: forall sys tc t v vOrig .
  (SysTC sys, MonadTC sys tc, DeBruijnLevel v, DeBruijnLevel vOrig, Analyzable sys t) =>
  Eta ->
  Coyoneda (Relation t) v ->
  Ctx Type sys vOrig ->
  Ctx (Twice2 Type) sys v ->
  (vOrig -> v) ->
  (v -> Maybe vOrig) ->
  t v ->
  ClassifExtraInput t vOrig ->
  ClassifExtraInput t v ->
  ClassifInfo (Twice1 (Classif t) v) ->
  String ->
  tc (t vOrig)
newRelatedAST eta relT gammaOrig gamma subst partialInv t2 extraT1orig extraT2 maybeCTs reason =
  case analyzableToken @sys @t of
    AnTokenTerm ->
      newRelatedMetaTerm eta relT gammaOrig gamma subst partialInv t2 maybeCTs
        (if unEta eta then MetaBlocked else MetaNeutral) reason
    AnTokenSys sysToken -> newRelatedMultimodeOrSysAST (Right sysToken)
      eta relT gammaOrig gamma subst partialInv t2 extraT1orig extraT2 maybeCTs reason
    AnTokenMultimode multimodeToken -> newRelatedMultimodeOrSysAST (Left multimodeToken)
      eta relT gammaOrig gamma subst partialInv t2 extraT1orig extraT2 maybeCTs reason
    _ -> newRelatedAST' relT gammaOrig gamma subst partialInv t2 extraT1orig extraT2 maybeCTs

newRelatedMetaTerm :: forall sys tc v vOrig .
  (SysTC sys, MonadTC sys tc, DeBruijnLevel v, DeBruijnLevel vOrig) =>
  Eta ->
  Coyoneda (ModedDegree sys) v ->
  Ctx Type sys vOrig ->
  Ctx (Twice2 Type) sys v ->
  (vOrig -> v) ->
  (v -> Maybe vOrig) ->
  Term sys v ->
  ClassifInfo (Twice1 (Type sys) v) ->
  MetaNeutrality ->
  String ->
  tc (Term sys vOrig)
newRelatedMetaTerm eta deg gammaOrig gamma subst partialInv t2 maybeTys neutrality reason = do
      t1orig <- newMetaTermNoCheck gammaOrig neutrality Nothing reason
      let t1 = subst <$> t1orig
      addNewConstraint
        (JudRel AnTokenTerm eta deg gamma (Twice1 t1 t2) (Twice1 U1 U1) maybeTys)
        reason
      return t1orig

---------------------------------------------------------------------

getSubstAndPartialInv :: forall sys v vOrig .
  (SysTC sys, DeBruijnLevel v, DeBruijnLevel vOrig) =>
  Dependencies sys v ->
  Either String (vOrig -> v, v -> Maybe vOrig)
getSubstAndPartialInv depcies = do
  let getVar2 :: Term sys v -> Maybe v
      getVar2 (Var2 v) = Just v
      getVar2 _ = Nothing
  --case sequenceA $ uncoy $ getVar2 . snd1 <$> (_ $ getDependencies $ depcies) of
  case sequenceA . uncoy . fmap (getVar2 . snd1) . getCompose . copopCoy' . getDependencies $ depcies of
    -- Some dependency is not a variable
    Nothing -> Left "Cannot solve meta-variable: it has non-variable dependencies."
    -- All dependencies are variables
    Just depcyVars -> do
      let (_, repeatedVars, _) = complex $ EqVar !<$> depcyVars
      case repeatedVars of
        -- Some variables occur twice
        _:_ -> Left "Cannot solve meta-variable: it has undergone contraction of dependencies."
        -- All variables are unique
        [] -> rnf depcyVars `seq` do
          let subst = flip atVarRev depcyVars
          let partialInv = join . fmap (forDeBruijnIndex . fromIntegral) . flip elemIndex (EqVar !<$> depcyVars) . EqVar
          return (subst, partialInv)

tryToSolveBy :: forall sys tc t v .
  (SysTC sys, MonadTC sys tc, DeBruijnLevel v, Solvable sys t) =>
  Ctx (Twice2 Type) sys v ->
  MetaNeutrality -> Int -> Dependencies sys v -> Maybe (Algorithm sys v) ->
  t v ->
  Classif t v ->
  Classif t v ->
  (forall vOrig . (DeBruijnLevel vOrig) =>
    Ctx Type sys vOrig ->
    (vOrig -> v) ->
    (v -> Maybe vOrig) ->
    tc (Maybe (t vOrig), Maybe String)
  ) ->
  tc (Maybe String)
tryToSolveBy gamma neut1 meta1 depcies1 maybeAlg1 t2 ct1 ct2 procedure = do
  depcies1 <- depcies1 & (_Wrapped' . cutCoyLens . _Wrapped' . traverse $ \ (d :*: depcy) ->
    fmap ((d :*:) . fst) $ runWriterT $ whnormalize (CtxOpaque $ d) depcy (Type $ Expr2 $ TermWildcard)
      "Trying to weak-head-normalize meta dependency to a variable"
    )
  let maybeProblem = case neut1 of
        MetaBlocked -> Nothing
        MetaNeutral -> case t2 of
          -- If a neutral meta is being equated to a constructor, eta-expansion is our only hope.
          --(Expr2 (TermCons _)) -> Just $ "Cannot solve neutral meta-variable with constructor expression."
          otherwise -> Nothing
  case maybeProblem of
    Just msg -> return $ Just msg
    Nothing -> solveMeta meta1 $ \ (gammaOrig :: Ctx Type sys vOrig) ->
      case getSubstAndPartialInv @sys @v @vOrig depcies1 of
        Left msg -> return (Nothing, Just msg)
        Right (subst, partialInv) -> procedure gammaOrig subst partialInv  

tryToSolveAgainstWHN :: forall sys tc t v .
  (SysTC sys, MonadTC sys tc, DeBruijnLevel v, Solvable sys t) =>
  Coyoneda (Relation t) v ->
  Ctx (Twice2 Type) sys v ->
  MetaNeutrality -> Int -> Dependencies sys v -> Maybe (Algorithm sys v) ->
  t v ->
  Classif t v ->
  Classif t v ->
  tc (Maybe String)
tryToSolveAgainstWHN rel gamma neut1 meta1 depcies1 maybeAlg1 t2 ct1 ct2 =
  tryToSolveBy gamma neut1 meta1 depcies1 maybeAlg1 t2 ct1 ct2 $ \ gammaOrig subst partialInv -> do
    t1orig <- newRelatedAST' rel gammaOrig gamma subst partialInv t2 U1 U1 (ClassifWillBe $ Twice1 ct1 ct2)
    return (Just t1orig, Nothing)
  {-do
  let maybeProblem = case neut1 of
        MetaBlocked -> Nothing
        MetaNeutral -> case t2 of
          -- If a neutral meta is being equated to a constructor, eta-expansion is our only hope.
          (Expr2 (TermCons _)) -> Just $ "Cannot solve neutral meta-variable with constructor expression."
          otherwise -> Nothing
  case maybeProblem of
    Just msg -> return $ Just msg
    Nothing -> solveMeta meta1 $ \ (gammaOrig :: Ctx Type sys vOrig Void) ->
      case getSubstAndPartialInv @sys @v @vOrig depcies1 of
        Left msg -> return (Nothing, Just msg)
        Right (subst, partialInv) -> do
          t1orig <- newRelatedAST' deg gammaOrig gamma subst partialInv t2 U1 U1 (ClassifWillBe $ Twice1 ty1 ty2)
          return (Just t1orig, Nothing)-}
  
{- Either solves the meta right away and returns 'Nothing', or does nothing and returns 'Just' why not.
   Never blocks.
-}
tryToSolveImmediately :: forall sys tc t v .
  (SysTC sys, MonadTC sys tc, DeBruijnLevel v, Solvable sys t) =>
  Ctx (Twice2 Type) sys v ->
  MetaNeutrality -> Int -> Dependencies sys v -> Maybe (Algorithm sys v) ->
  t v ->
  Classif t v ->
  Classif t v ->
  tc (Maybe String)
tryToSolveImmediately gamma neut1 meta1 depcies1 maybeAlg1 t2 ct1 ct2 = have (witClassif @sys @t analyzableToken) $
  tryToSolveBy gamma neut1 meta1 depcies1 maybeAlg1 t2 ct1 ct2 $ \ gammaOrig subst partialInv -> do
    --whnormalize the type (classifier) a bit to decrease the amount of variables you depend on
    let extraCT2 = extraClassif @sys @t (ctx'mode gamma) t2 U1
    cct2 <- newMetaClassif4astNoCheck (sndCtx gamma) ct2 extraCT2 "Inferring a classifier's classifier."
      -- It is assumed that a classifier's classifier needs no metas.
    (whnct2, _) <- runWriterT $ whnormalizeAST (sndCtx gamma) ct2 extraCT2 cct2 "Weak-head-normalize type of solution."
    --solve
    case sequenceA $ partialInv <$> astAlreadyChecked @sys t2 ct2 of
      Nothing ->
        return (Nothing, Just "Cannot solve meta-variable immediately: candidate solution may have more dependencies.")
      Just t2orig -> return (Just t2orig, Nothing)
  {-do
  let maybeProblem = case neut1 of
        MetaBlocked -> Nothing
        MetaNeutral -> case t2 of
          -- If a neutral meta is being equated to a constructor, eta-expansion is our only hope.
          (Expr2 (TermCons _)) -> Just $ "Cannot solve neutral meta-variable with constructor expression."
          otherwise -> Nothing
  case maybeProblem of
    Just msg -> return $ Just msg
    Nothing -> solveMeta meta1 $ \ (gammaOrig :: Ctx Type sys vOrig Void) ->
      case getSubstAndPartialInv @sys @v @vOrig depcies1 of
        Left msg -> return (Nothing, Just msg)
        Right (subst, partialInv) -> case sequenceA $ partialInv <$> t2 of
          Nothing ->
            return (Nothing, Just "Cannot solve meta-variable immediately: candidate solution may have more dependencies.")
          Just t2orig -> return (Just t2orig, Nothing)-}
