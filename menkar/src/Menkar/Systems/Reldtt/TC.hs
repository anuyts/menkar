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
import Menkar.Systems.Reldtt.Fine
import Menkar.Systems.Reldtt.Analyzer
import Menkar.Systems.Reldtt.Scoper
import Menkar.Systems.Reldtt.WHN

import Control.Monad.DoUntilFail
import Control.Exception.AssertFalse
import Data.Functor.Coerce

import Control.Monad.Trans.Class
import Control.Monad.Writer.Class
import Control.Monad.Trans.Writer.Lazy
import Control.Monad.Trans.Maybe
import Control.Monad.State.Lazy
import Control.Applicative
import Control.Lens
import Data.Void
import GHC.Generics
import Data.Functor.Compose
import Data.Maybe
import Data.List.Ordered

{-tryToSolveChainModty :: forall tc v .
  (MonadTC Reldtt tc, DeBruijnLevel v) =>
  Ctx (Twice2 Type) Reldtt v Void ->
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

  -- Relatedness-checker --
  -------------------------

  checkUnanalyzableSysASTRel' sysError eta rel gamma (Twice1 t1 t2 :: Twice1 t v) (Twice1 extraT1 extraT2) maybeCTs =
    case (sysError, analyzableToken @Reldtt @t, t1, t2) of
      (AnErrorModtySnout, AnTokenSys AnTokenModtySnout, Const snout1, Const snout2) -> do
        let (==/<=) = case rel of
              Const ModEq -> (==)
              Const ModLeq -> (<=)
        when (not $ snout1 ==/<= snout2) $ tcFail "False."
      (AnErrorModtySnout, _, _, _) -> unreachable
      
  checkMultimodeOrSysASTRel token eta relT gamma ts@(Twice1 t1 t2) extraTs@(Twice1 extraT1 extraT2) maybeCTs = case token of
    Left AnTokenMode -> byAnalysis
    Left AnTokenModality -> do
      (t1, metasT1) <- runWriterT $ whnormalizeChainModty (fstCtx gamma) t1 "Weak-head-normalizing 1st modality." 
      (t2, metasT2) <- runWriterT $ whnormalizeChainModty (sndCtx gamma) t2 "Weak-head-normalizing 2nd modality."
      case (metasT1, metasT2) of
        ([], []) -> checkASTRel' eta relT gamma (Twice1 t1 t2) extraTs maybeCTs
        (_ , _ ) -> tcBlock "Cannot solve inequality: one side is blocked on a meta-variable."
    Left AnTokenDegree -> do
      (t1, metasT1) <- runWriterT $ whnormalizeReldttDegree (fstCtx gamma) t1 "Weak-head-normalizing 1st degree."
      (t2, metasT2) <- runWriterT $ whnormalizeReldttDegree (sndCtx gamma) t2 "Weak-head-normalizing 2nd degree."
      case (metasT1, metasT2) of
        ([], []) -> checkASTRel' eta relT gamma (Twice1 t1 t2) extraTs maybeCTs
        otherwise -> tcBlock "Cannot solve relation: one side is blocked on a meta-variable."
    Right AnTokenModeTerm -> byAnalysis
    Right AnTokenModtyTerm -> byAnalysis
    Right AnTokenModtySnout -> unreachable
    Right AnTokenModtyTail -> unreachable
    Right AnTokenKnownModty -> do
      case relKnownModty (getConst relT) t1 t2 of
        Nothing -> -- This may occur when something is ill-typed.
          tcFail "Modalities are presumed to have equal (co)domain."
        Just True -> return ()
        Just False -> tcFail "False."
    where
      byAnalysis :: forall tc . (MonadTC Reldtt tc) => tc ()
      byAnalysis = checkASTRel' eta relT gamma ts extraTs maybeCTs

  -- Solver --
  ------------

  newRelatedSysASTUnanalyzable' sysError relT gammaOrig gamma subst partialInv (t2 :: t v) extraT1orig extraT2 maybeCTs =
    case (sysError, analyzableToken @Reldtt @t, t2) of
      (AnErrorModtySnout, AnTokenSys AnTokenModtySnout, Const snout2) -> case getConst relT of
        ModLeq -> unreachable -- There's no unique solution here and there are no metas.
        ModEq -> return $ Const snout2
      (AnErrorModtySnout, _, _) -> unreachable

  newRelatedMultimodeOrSysAST token eta relT gammaOrig gamma subst partialInv t2 extraT1orig extraT2 maybeCTs reason =
    case token of
      Left AnTokenMode -> byAnalysis
      Left AnTokenModality -> case getConst relT of
        ModEq -> byAnalysis
        ModLeq -> _
        
    where
      byAnalysis :: forall tc . (MonadTC Reldtt tc) => tc _
      byAnalysis = newRelatedAST' relT gammaOrig gamma subst partialInv t2 extraT1orig extraT2 maybeCTs
