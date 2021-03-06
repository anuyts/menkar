module Menkar.Systems.Reldtt.TC where

import Menkar.Basic
import Menkar.Analyzer
import Menkar.WHN
import Menkar.TC
import Menkar.System.Fine
import Menkar.System.Scoper
import Menkar.System.WHN
import Menkar.System.TC
import Menkar.Fine
import Menkar.Monad
import Menkar.Systems.Reldtt.Basic
import Menkar.Systems.Reldtt.Fine
import Menkar.Systems.Reldtt.Analyzer
import Menkar.Systems.Reldtt.Scoper
import Menkar.Systems.Reldtt.WHN

import Control.Monad.DoUntilFail
import Control.Exception.AssertFalse
import Data.Functor.Coerce
import Data.Functor.Coyoneda.NF

import Control.Monad.Trans.Class
import Control.Monad.Writer.Class
import Control.Monad.Trans.Writer.Strict
import Control.Monad.Trans.Maybe
import Control.Monad.State.Strict
import Control.Applicative
import Control.Lens
import Data.Void
import GHC.Generics
import Data.Functor.Compose
import Data.Functor.Constant
import Data.Maybe
import Data.List.Ordered

{-tryToSolveChainModty :: forall tc v .
  (MonadTC Reldtt tc, DeBruijnLevel v) =>
  Ctx (Twice2 Type) Reldtt v ->
  ChainModty v ->
  ChainModty v ->
  ClassifInfo (Twice1 (ReldttMode :*: ReldttMode) v) ->
  tc ()
tryToSolveChainModty gamma chmu1blocked chmu2 maybeDomCods = case chmu1blocked of
  ChainModtyDisguisedAsTerm dom cod t1 -> checkTermRel
    (Eta False)
    (modedEqDeg $ ReldttMode $ BareMode $ ModeTermZero)
    gamma
    (Twice1 t1 (Expr2 $ TermSys $ SysTermChainModtyInDisguise $ chmu2))
    (maybeDomCods <&> mapTwice1 (\ (dom :*: cod) -> BareSysType $ SysTypeChainModtyDisguisedAsTerm dom cod))
  otherwise -> tcBlock "Cannot solve relation: one side is blocked on a meta-variable."-}

instance SysTC Reldtt where

  -- Judgement-checker --
  -----------------------

  checkSysJudgement jud = case jud of {}

  -- Type-checker --
  ------------------

  checkSysASTUnanalyzable sysError gamma (t :: t v) extraT maybeCT = case (sysError, analyzableToken @Reldtt @t, t) of
    (AnErrorModtySnout, AnTokenSys AnTokenModtySnout, Const (ModtySnout idom icod krevdegs)) -> do
      unless (isSortedBy (>=) krevdegs) $
        tcFail "Degrees are not ordered."
      unless (all (\ kdeg -> (kdeg < KnownDeg idom) || (kdeg >= KnownDegOmega)) krevdegs) $
        tcFail "A degree is unavailable in the domain."
      when (any (== KnownDegProblem) krevdegs) $ tcFail "Problematic degree encountered."
      return U1
    (AnErrorModtySnout, _, _) -> unreachable
    (AnErrorChainModtyMeta, AnTokenMultimode AnTokenModality, chmu@(ChainModtyMeta dom cod meta depcies)) -> do
      addNewConstraint
        (Jud analyzableToken gamma dom U1 (ClassifWillBe U1))
        "Modality metavariable: checking domain annotation."
      addNewConstraint
        (Jud analyzableToken gamma cod U1 (ClassifWillBe U1))
        "Modality metavariable: checking codomain annotation."
      maybeChmu <- awaitMeta @Reldtt @_ @ChainModty "I want to know what modality I'm supposed to type-check." meta depcies
      chmu' <- case maybeChmu of
        Just chmu' -> return chmu'
        Nothing -> do
          -- request eta-expansion.
          addNewConstraint
            (JudEta analyzableToken gamma chmu U1 (fromClassifInfo (_modality'dom chmu :*: _modality'cod chmu) maybeCT))
            "Eta-expand meta if possible"
          tcBlock "I want to know what modality I'm supposed to type-check."
      addNewConstraint
        (Jud analyzableToken gamma chmu' U1 (ClassifMustBe $ dom :*: cod))
        "Look up meta."
      --withParent childConstraint $ checkAST gamma chmu' U1 (classifMust2will maybeCT)
      return $ dom :*: cod
    (AnErrorChainModtyMeta, _, _) -> unreachable
    (AnErrorChainModtyAlreadyChecked, AnTokenMultimode AnTokenModality,
     chmu@(ChainModtyAlreadyChecked dom cod chmuChecked)) -> return $ dom :*: cod
    (AnErrorChainModtyAlreadyChecked, _, _) -> unreachable

  -- Relatedness-checker --
  -------------------------

  checkUnanalyzableSysASTRel' sysError eta rel gamma (Twice1 t1 t2 :: Twice1 t v) (Twice1 extraT1 extraT2) maybeCTs =
    case (sysError, analyzableToken @Reldtt @t, t1, t2) of
      (AnErrorModtySnout, AnTokenSys AnTokenModtySnout, Const snout1, Const snout2) -> do
        let (==/<=) = case uncoy rel of
              Const ModEq -> (==)
              Const ModLeq -> (<=)
        when (not $ snout1 ==/<= snout2) $ tcFail "False."
      (AnErrorModtySnout, _, _, _) -> unreachable
      (AnErrorChainModtyMeta, AnTokenMultimode AnTokenModality, _, _) ->
        unreachable -- terms are neutral at this point
      (AnErrorChainModtyMeta, _, _, _) -> unreachable
      (AnErrorChainModtyAlreadyChecked, AnTokenMultimode AnTokenModality, _, _) ->
        unreachable -- terms are neutral at this point
      (AnErrorChainModtyAlreadyChecked, _, _, _) -> unreachable
      
  checkMultimodeOrSysASTRel token eta relT gamma ts@(Twice1 t1 t2) extraTs@(Twice1 extraT1 extraT2) maybeCTs = case token of
    Left AnTokenMode -> byAnalysis
    Left AnTokenModality -> do
      let dom1 = _modality'dom t1
      let cod1 = _modality'cod t1
      let dom2 = _modality'dom t2
      let cod2 = _modality'cod t2
      (t1, metasT1) <- runWriterT $ whnormalizeChainModty t1 "Weak-head-normalizing 1st modality." 
      (t2, metasT2) <- runWriterT $ whnormalizeChainModty t2 "Weak-head-normalizing 2nd modality."
      parent <- defConstraint
        (JudRel analyzableToken eta relT gamma (Twice1 t1 t2) extraTs maybeCTs)
        "Weak-head-normalizing both sides."
      withParent parent $ do
        -- If one side is a meta and the other is WHN, then we can solve immediately.
        solved <- do
          case getConst $ uncoy relT of
            ModLeq -> return False
            ModEq -> case (metasT1, metasT2, t1, t2) of
              (_:_, [] , ChainModtyMeta _ _ meta1 depcies1, _) ->
                isNothing <$> tryToSolveImmediately          gamma  MetaBlocked meta1 depcies1 Nothing t2
                   (dom1 :*: cod1)
                   (dom2 :*: cod2)
              ([] , _:_, _, ChainModtyMeta _ _ meta2 depcies2) ->
                isNothing <$> tryToSolveImmediately (flipCtx gamma) MetaBlocked meta2 depcies2 Nothing t1
                   (dom2 :*: cod2)
                   (dom1 :*: cod1)
              otherwise -> return False
        -- If this failed, then we try eta and otherwise compare normal chains.
        unless solved $ do
          etaSolved <- if not (unEta eta)
            then return False
            else do
              (cod1, metasCod1) <- runWriterT $ whnormalizeAST @Reldtt @_ @_ @ReldttMode
                cod1 U1 U1 "Weak-head-normalize codomain (of 1st modality)"
              case (cod1, metasCod1) of
                (_, _:_) -> tcBlock $ "Need to know codomain: If it's zero, I can apply eta."
                (ReldttMode (BareMode ModeTermZero), _) -> return True
                (_, _) -> return False
          unless etaSolved $ case (metasT1, metasT2, t1, t2) of
            ([], _  , ChainModtyTerm _ _ _, _) -> unreachable
            (_  , [] , _, ChainModtyTerm _ _ _) -> unreachable
            ([] , [] , _, _) -> checkASTRel' eta relT gamma (Twice1 t1 t2) (Twice1 U1 U1) maybeCTs
            (_:_, [] , _, _) -> tcBlock $ "Cannot solve relation: left side is blocked."
            ([] , _:_, _, _) -> tcBlock $ "Cannot solve relation: right side is blocked."
            (_:_, _:_, _, _) -> tcBlock $ "Cannot solve inequality: both sides are blocked on a meta-variable."
    Left AnTokenDegree -> do
      (t1, metasT1) <- runWriterT $ whnormalizeReldttDegree t1 "Weak-head-normalizing 1st degree."
      (t2, metasT2) <- runWriterT $ whnormalizeReldttDegree t2 "Weak-head-normalizing 2nd degree."
      newParent <- defConstraint
        (JudRel analyzableToken eta relT gamma (Twice1 t1 t2) extraTs maybeCTs)
        "Weak-head-normalizing both sides."
      withParent newParent $ case (metasT1, metasT2) of
        ([], []) -> checkASTRel' eta relT gamma (Twice1 t1 t2) extraTs maybeCTs
        otherwise -> tcBlock "Cannot solve relation: one side is blocked on a meta-variable."
    Right AnTokenModeTerm -> byAnalysis
    Right AnTokenModtyTerm -> byAnalysis
    Right AnTokenModtySnout -> unreachable
    Right AnTokenModtyTail -> unreachable
    Right AnTokenKnownModty -> do
      related <- relKnownModty (getConst $ uncoy relT) t1 t2 "Checking (in)equality of modalities."
      case related of
        Nothing -> -- This may occur when something is ill-typed.
          tcFail "Modalities are presumed to have equal (co)domain."
        Just Nothing ->
          tcBlock $ "Cannot solve relation: something is blocked."
        Just (Just True) -> return ()
        Just (Just False) -> tcFail "False."
    where
      byAnalysis :: forall tc . (MonadTC Reldtt tc) => tc ()
      byAnalysis = checkASTRel' eta relT gamma ts extraTs maybeCTs

  -- Solver --
  ------------

  newRelatedSysASTUnanalyzable' sysError relT gammaOrig gamma subst partialInv (t2 :: t v) extraT1orig extraT2 maybeCTs =
    case (sysError, analyzableToken @Reldtt @t, t2) of
      (AnErrorModtySnout, AnTokenSys AnTokenModtySnout, Const snout2) -> case getConst $ uncoy relT of
        ModLeq -> unreachable -- There's no unique solution here and there are no metas.
        ModEq -> return $ Const snout2
      (AnErrorModtySnout, _, _) -> unreachable
      (AnErrorChainModtyMeta, AnTokenMultimode AnTokenModality, _) ->
        unreachable -- terms are neutral at this point
      (AnErrorChainModtyMeta, _, _) -> unreachable
      (AnErrorChainModtyAlreadyChecked, AnTokenMultimode AnTokenModality, _) ->
        unreachable -- terms are neutral at this point
      (AnErrorChainModtyAlreadyChecked, _, _) -> unreachable

  newRelatedMultimodeOrSysAST token eta relT gammaOrig gamma subst partialInv t2 extraT1orig extraT2 maybeCTs reason =
    case token of
      Left AnTokenMode -> byAnalysis
      Left AnTokenModality -> do
        dom1orig <- newRelatedMetaMode (Eta True) gammaOrig gamma subst partialInv (_chainModty'dom t2) "Inferring domain."
        cod1orig <- newRelatedMetaMode (Eta True) gammaOrig gamma subst partialInv (_chainModty'cod t2) "Inferring codomain."
        t1orig <- newMetaChainModtyNoCheck gammaOrig dom1orig cod1orig reason
        let t1 = subst <$> t1orig
        addNewConstraint
          (JudRel (AnTokenMultimode AnTokenModality) eta relT gamma (Twice1 t1 t2) (Twice1 U1 U1) maybeCTs)
          reason
        return t1orig
      Left AnTokenDegree -> byAnalysis
      Right AnTokenModeTerm -> byAnalysis
      Right AnTokenModtyTerm -> byAnalysis
      Right AnTokenModtySnout -> unreachable
      Right AnTokenModtyTail -> unreachable
      Right AnTokenKnownModty -> unreachable
      {-
      Right AnTokenModtySnout -> case getConst relT of
        ModEq -> return $ Const $ getConst t2
        ModLeq -> unreachable
      Right AnTokenModtyTail -> case getConst relT of
        ModEq -> byAnalysis
        ModLeq -> unreachable
      Right AnTokenModtyKnown -> case getConst relT of
        ModEq -> byAnalysis
        ModLeq -> unreachable
      -}
    where
      byAnalysis :: forall tc . (MonadTC Reldtt tc) => tc _
      byAnalysis = newRelatedAST' relT gammaOrig gamma subst partialInv t2 extraT1orig extraT2 maybeCTs

  -- Eta --
  ---------

  checkEtaMultimodeOrSys token gamma t extraT ct = case token of
    Left AnTokenModality -> do
      let dom :*: cod = ct
      (cod, metasCod) <- runWriterT $ whnormalizeMode cod "Want to know if codomain is zero"
      case (cod, metasCod) of
        (_, _:_) -> tcBlock $ "Need to know if codomain is zero."
        (ReldttMode (BareMode (ModeTermZero)), _) -> do
          let (ChainModtyMeta dom cod meta depcies) = t
          tryToSolveImmediately
            (duplicateCtx gamma)
            MetaBlocked
            meta
            depcies
            Nothing -- no algorithm
            (ChainModtyKnown $ forgetKnownModty $ dom) -- eta-expansion
            ct
            ct
          return True
        otherwise -> return False
    otherwise -> unreachable -- There are no other solvable AST types.

  etaExpandSysType useHoles gamma t systy = case systy of
    SysTypeMode -> return $ Just Nothing
    SysTypeModty dom cod -> do
      let mu = t
      chmu <- case useHoles of
        UseHoles -> newMetaChainModty gamma dom cod "Infer underlying modality represented by this term."
        UseEliminees -> return $ ChainModtyTerm dom cod mu
      return $ Just $ Just $ BareModty $ ModtyTermChain $ chmu

      {-do
      (cod, metasCod) <- runWriterT $ whnormalizeMode gamma cod "Want to know if codomain is zero."
      case (cod, metasCod) of
        (_, _:_) -> return Nothing
        (ReldttMode (BareMode (ModeTermZero)), _) -> return $ Just $ Just $ BareKnownModty $
          forgetKnownModty $ cod
        (_, _) -> do
          chmu <- case useHoles of
            UseHoles -> ChainModtyTerm dom cod <$>
              newMetaTerm gamma (BareSysType $ SysTypeModty dom cod) MetaBlocked "Infer chain modality."
            UseEliminees -> return $ ChainModtyTerm dom cod t
          return $ Just $ Just $ BareModty $ ModtyTermChain $ chmu-}

newMetaChainModty :: 
  (DeBruijnLevel v, MonadTC Reldtt tc) =>
  Ctx Type Reldtt v ->
  Mode Reldtt v ->
  Mode Reldtt v ->
  String ->
  tc (ChainModty v)
newMetaChainModty gamma dom cod reason = do
  chmu <- newMetaChainModtyNoCheck gamma dom cod reason
  addNewConstraint
    (Jud analyzableToken gamma chmu U1 (ClassifMustBe $ dom :*: cod))
    reason
  return chmu
