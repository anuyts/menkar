module Menkar.Systems.Reldtt.WHN where

import Menkar.Basic
import Menkar.Analyzer
import Menkar.WHN
import Menkar.System.Fine
import Menkar.System.Scoper
import Menkar.System.WHN
import Menkar.Fine
import Menkar.Monad
import Menkar.Systems.Reldtt.Basic
import Menkar.Systems.Reldtt.Fine
import Menkar.Systems.Reldtt.Analyzer
import Menkar.Systems.Reldtt.Scoper

import Control.Monad.DoUntilFail
import Control.Exception.AssertFalse
import Data.Functor.Coerce

import Control.Monad.Trans.Class
import Control.Monad.Writer.Class
import Control.Monad.Trans.Writer.Strict hiding (listen, tell)
import Control.Monad.Trans.Maybe
import Control.Monad.State.Strict
import Control.Applicative
import Control.Lens
import Data.Void
import GHC.Generics
import Data.Functor.Compose
import Data.Maybe

{-| Compare known modalities, assuming they have the same type.
    Return a boolean if they compare, or @Nothing@ in case of problems
    (not metavariable-related problems, but ACTUAL problems).
-}
relKnownModty :: forall v . ModRel -> KnownModty v -> KnownModty v -> Maybe Bool
relKnownModty rel kmu1@(KnownModty snout1 tail1) kmu2@(KnownModty snout2 tail2) = do
          (kmu1, kmu2) <-
            case compare (_modtySnout'dom $ _knownModty'snout kmu1) (_modtySnout'dom $ _knownModty'snout kmu2) of
              LT -> (, kmu2) <$> forceDom snout1 tail1 (_modtySnout'dom snout2) (_modtyTail'dom tail2)
              EQ -> Just (kmu1, kmu2)
              GT -> (kmu1, ) <$> forceDom snout2 tail2 (_modtySnout'dom snout1) (_modtyTail'dom tail1)
          (kmu1, kmu2) <-
            case compare (_modtySnout'cod $ _knownModty'snout kmu1) (_modtySnout'cod $ _knownModty'snout kmu2) of
              LT -> (, kmu2) <$> forceCod snout1 tail1 (_modtySnout'cod snout2) (_modtyTail'cod tail2)
              EQ -> Just (kmu1, kmu2)
              GT -> (kmu1, ) <$> forceCod snout2 tail2 (_modtySnout'cod snout1) (_modtyTail'cod tail1)
          let opSnout = case rel of
                ModEq -> (==)
                ModLeq -> (<=)
          let relSnout = and $ getZipList $
                (opSnout) <$> ZipList (_modtySnout'degreesReversed $ _knownModty'snout kmu1)
                          <*> ZipList (_modtySnout'degreesReversed $ _knownModty'snout kmu2)
          return $ relSnout && relTail rel kmu1 kmu2

----------------------------------

-- | composition
compModtySnout :: ModtySnout -> KnownModty v -> ModtySnout
compModtySnout (ModtySnout kmid kcod []) mu =
  ModtySnout (_modtySnout'dom $ _knownModty'snout $ mu) kcod []
compModtySnout (ModtySnout kmid kcod krevdegs) mu =
  ModtySnout (_modtySnout'dom $ _knownModty'snout $ mu) kcod $ flip knownGetDeg mu <$> krevdegs

-- | composition
compModtyTail :: ModtyTail v -> ModtyTail v -> ModtyTail v
compModtyTail (TailCont d) tail1 = tail1
compModtyTail tail2 (TailCont d) = tail2
compModtyTail TailEmpty TailEmpty = TailEmpty
compModtyTail TailEmpty (TailDisc   _) = TailEmpty
--compModtyTail TailEmpty (TailCodisc _) = TailEmpty
compModtyTail TailEmpty (TailForget ddom) = TailForget ddom
compModtyTail TailEmpty (TailDiscForget   ddom _) = TailForget ddom
--compModtyTail TailEmpty (TailCodiscForget ddom _) = TailForget ddom
compModtyTail (TailDisc   dcod) TailEmpty = TailDisc dcod
compModtyTail (TailDisc   dcod) (TailDisc   _) = TailDisc dcod
--compModtyTail (TailDisc   dcod) (TailCodisc _) = TailDisc dcod
compModtyTail (TailDisc   dcod) (TailForget ddom) = TailDiscForget ddom dcod
compModtyTail (TailDisc   dcod) (TailDiscForget   ddom _) = TailDiscForget ddom dcod
--compModtyTail (TailDisc   dcod) (TailCodiscForget ddom _) = TailDiscForget ddom dcod
{-compModtyTail (TailCodisc dcod) TailEmpty = TailCodisc dcod
compModtyTail (TailCodisc dcod) (TailDisc   _) = TailCodisc dcod
compModtyTail (TailCodisc dcod) (TailCodisc _) = TailCodisc dcod
compModtyTail (TailCodisc dcod) (TailForget ddom) = TailCodiscForget ddom dcod
compModtyTail (TailCodisc dcod) (TailDiscForget   ddom _) = TailCodiscForget ddom dcod
compModtyTail (TailCodisc dcod) (TailCodiscForget ddom _) = TailCodiscForget ddom dcod-}
compModtyTail (TailForget _) TailEmpty = TailEmpty
compModtyTail (TailForget _) (TailDisc   _) = TailEmpty
--compModtyTail (TailForget _) (TailCodisc _) = TailEmpty
compModtyTail (TailForget _) (TailForget ddom) = TailForget ddom
compModtyTail (TailForget _) (TailDiscForget   ddom _) = TailForget ddom
--compModtyTail (TailForget _) (TailCodiscForget ddom _) = TailForget ddom
compModtyTail (TailDiscForget   _ dcod) TailEmpty = TailDisc dcod
compModtyTail (TailDiscForget   _ dcod) (TailDisc   _) = TailDisc dcod
--compModtyTail (TailDiscForget   _ dcod) (TailCodisc _) = TailDisc dcod
compModtyTail (TailDiscForget   _ dcod) (TailForget ddom) = TailDiscForget ddom dcod
compModtyTail (TailDiscForget   _ dcod) (TailDiscForget   ddom _) = TailDiscForget ddom dcod
--compModtyTail (TailDiscForget   _ dcod) (TailCodiscForget ddom _) = TailDiscForget ddom dcod
{-compModtyTail (TailCodiscForget _ dcod) TailEmpty = TailCodisc dcod
compModtyTail (TailCodiscForget _ dcod) (TailDisc   _) = TailCodisc dcod
compModtyTail (TailCodiscForget _ dcod) (TailCodisc _) = TailCodisc dcod
compModtyTail (TailCodiscForget _ dcod) (TailForget ddom) = TailCodiscForget ddom dcod
compModtyTail (TailCodiscForget _ dcod) (TailDiscForget   ddom _) = TailCodiscForget ddom dcod
compModtyTail (TailCodiscForget _ dcod) (TailCodiscForget ddom _) = TailCodiscForget ddom dcod-}
compModtyTail TailProblem _ = TailProblem
compModtyTail _ TailProblem = TailProblem

compKnownModty :: KnownModty v -> KnownModty v -> KnownModty v
compKnownModty mu2@(KnownModty snout2 tail2) mu1@(KnownModty snout1 tail1) =
  let maybeStuff = case compare (_modtySnout'cod snout1) (_modtySnout'dom snout2) of
                     LT -> (, mu2) <$> forceCod snout1 tail1 (_modtySnout'dom snout2) (_modtyTail'dom tail2)
                     EQ -> Just (mu1, mu2)
                     GT -> (mu1, ) <$> forceDom snout2 tail2 (_modtySnout'cod snout1) (_modtyTail'cod tail1)
  in case maybeStuff of
       Nothing -> problemKnownModty
       Just (mu1@(KnownModty snout1 tail1), mu2@(KnownModty snout2 tail2)) ->
         let snoutComp = compModtySnout snout2 mu1
             tailComp = compModtyTail tail2 tail1
         in  KnownModty snoutComp tailComp

compChainModty :: ChainModty v -> ChainModty v -> ChainModty v
compChainModty (ChainModtyLink kmu tnu chrho) chsigma =
  ChainModtyLink kmu tnu $ compChainModty chrho chsigma
compChainModty (ChainModtyKnown kmu) (ChainModtyLink knu trho chsigma) =
  ChainModtyLink (kmu `compKnownModty` knu) trho chsigma
compChainModty (ChainModtyKnown kmu) (ChainModtyKnown knu) =
  ChainModtyKnown (kmu `compKnownModty` knu)
compChainModty chmu chnu =
  ChainModtyTerm (_chainModty'dom chnu) (_chainModty'cod chmu) $ BareModty $ ModtyTermComp chmu chnu

{-
whnormalizeComp :: forall whn v .
  (MonadWHN Reldtt whn, MonadWriter [Int] whn, DeBruijnLevel v) =>
  Constraint Reldtt ->
  Ctx Type Reldtt v ->
  Term Reldtt v ->
  Term Reldtt v ->
  Term Reldtt v ->
  Type Reldtt v ->
  String ->
  whn (Term Reldtt v)
whnormalizeComp gamma mu2 dmid mu1 ty reason = do
  whnTy <- whnormalizeType gamma ty reason
  let giveUp = return $ BareModty $ ModtyTermComp mu2 dmid mu1
  case unType whnTy of
    Expr2 (TermSys (SysTypeModty ddom dcod)) -> do
      whnMu1 <- whnormalize gamma mu1 (Type $ Expr2 $ TermSys $ SysTypeModty ddom dmid) reason
      whnMu2 <- whnormalize gamma mu2 (Type $ Expr2 $ TermSys $ SysTypeModty dmid dcod) reason
      case (whnMu1, whnMu2) of
        (BareModty (ModtyTermUnavailable ddom' dmid'), _) ->
          return $ BareModty $ ModtyTermUnavailable ddom' dcod -- USING THE TYPE!
        (_, BareModty (ModtyTermUnavailable dmid' dcod')) ->
          return $ BareModty $ ModtyTermUnavailable ddom dcod' -- USING THE TYPE!
        (BareModty (ModtyTerm snout2 tail2), BareModty (ModtyTerm snout1 tail1)) -> do
          let maybeStuff = case compare (_modtySnout'cod snout1) (_modtySnout'dom snout2) of
                LT -> (, (snout2, tail2)) <$> forceCod snout1 tail1 (_modtySnout'dom snout2) (_modtyTail'dom tail2)
                EQ -> Just ((snout1, tail1), (snout2, tail2))
                GT -> ((snout1, tail1), ) <$> forceDom snout2 tail2 (_modtySnout'cod snout1) (_modtyTail'cod tail1)
          case maybeStuff of
            Nothing -> Expr2 . TermProblem <$> giveUp
            Just ((snout1, tail1), (snout2, tail2)) -> do
              let snoutComp = compModtySnout snout2 snout1
              let tailComp = compModtyTail tail2 tail1
              return $ BareModty $ ModtyTerm snoutComp tailComp
        (_, _) -> return $ BareModty $ ModtyTermComp whnMu2 dmid whnMu1
    otherwise -> giveUp
-}

---------------------

{-
-- | Beware that the omega-case is not really handled!
knownGetDegSnout :: KnownDeg -> ModtySnout -> KnownDeg
knownGetDegSnout KnownDegEq mu = KnownDegEq
knownGetDegSnout (KnownDeg i) (ModtySnout kdom kcod krevdegs) = krevdegs !! (length krevdegs - i - 1)
knownGetDegSnout KnownDegOmega mu = KnownDegOmega
knownGetDegSnout KnownDegTop mu = KnownDegTop
knownGetDegSnout KnownDegProblem mu = KnownDegProblem
-}

knownGetDeg :: KnownDeg -> KnownModty v -> KnownDeg
knownGetDeg KnownDegEq _ = KnownDegEq
knownGetDeg KnownDegTop _ = KnownDegTop
knownGetDeg KnownDegProblem _ = KnownDegProblem
knownGetDeg (KnownDeg i) (KnownModty snout@(ModtySnout idom icod krevdegs) tail) =
  if i < icod
  then krevdegs !! (icod - i - 1)
  else case tail of
    TailEmpty -> KnownDegProblem
    TailDisc dcod -> snoutMax
    TailForget ddom -> KnownDegProblem
    TailDiscForget ddom dcod -> snoutMax
    TailCont d -> KnownDeg (i - icod + idom)
    TailProblem -> KnownDegProblem
  where snoutMax = _snout'max snout
knownGetDeg KnownDegOmega mu@(KnownModty snout@(ModtySnout idom icod krevdegs) tail) = case tail of
  TailEmpty -> KnownDegProblem
  TailDisc dcod -> snoutMax
  TailForget ddom -> KnownDegProblem
  TailDiscForget ddom dcod -> snoutMax
  TailCont d -> KnownDegOmega
  TailProblem -> KnownDegProblem
  where snoutMax = _snout'max snout

---------------------

{-| Fails (returns Nothing) for modalities with a discrete tail of neutral length.
    Precondition: argument has been whnormalized to the extent possible.
-}
knownApproxLeftAdjointProj :: KnownModty v -> Maybe (KnownModty v)
knownApproxLeftAdjointProj kmu@(KnownModty snout@(ModtySnout idom icod krevdegs) tail) =
  {- Fields:
     _1: number of degrees popped from the input modality, minus one.
     _2: remaining tail of the input modality
     _3: already constructed part of output modality, REVERSED
     _4: length of _3
  -}
  let (_, _, krevdegs', _) = flip execState (-1, reverse krevdegs, [], 0) $
        doUntilFail $ do
          remainingTail <- use _2
          threshold <- use _4
          if threshold == idom
            then return False
            else True <$ case remainingTail of
              nextDeg : remainingTail' -> if nextDeg > KnownDeg threshold
                then do -- Write a degree, increase the length
                  nextDeg' <- use _1
                  _3 %= (nextDeg' :)
                  _4 += 1
                else do -- Pop a degree, increase the pop-counter
                  _2 .= remainingTail'
                  _1 += 1
              [] -> do -- Write a degree, increase the length
                nextDeg' <- use _1
                _3 %= (nextDeg' :)
                _4 += 1
      snout' = ModtySnout icod idom (int2deg <$> krevdegs')
      snoutCohpi' = ModtySnout icod idom $ krevdegs' <&> \ i -> if i == (idom - 1) then KnownDegOmega else int2deg i
  in  case tail of
        TailEmpty -> Just $ KnownModty snout' $ TailEmpty
        TailDisc dcod -> case dcod of
          ReldttMode BareModeOmega -> Just $ KnownModty snoutCohpi' $ TailForget dcod
          _ -> case krevdegs of
            -- We can read the tail as TailCodisc
            KnownDegTop : _ -> Just $ KnownModty snout' $ TailForget dcod
            _ -> Nothing
        TailForget ddom -> Just $ KnownModty snout' $ TailDisc ddom
        TailDiscForget ddom dcod -> case dcod of
          ReldttMode BareModeOmega -> Just $ KnownModty snoutCohpi' $ TailDiscForget dcod ddom
          _ -> case krevdegs of
            -- We can read the tail as TailCodiscForget
            KnownDegTop : _ -> Just $ KnownModty snout' $ TailDiscForget dcod ddom
            _ -> Nothing
        TailCont d -> Just $ KnownModty snout' $ TailCont d
        TailProblem -> Just $ KnownModty snout' $ TailProblem
  where int2deg :: Int -> KnownDeg
        int2deg (-1) = KnownDegEq
        int2deg i = KnownDeg i

---------------------

whnormalizeModtyTail :: forall whn v .
  (MonadWHN Reldtt whn, MonadWriter [Int] whn, DeBruijnLevel v) =>
  Ctx Type Reldtt v ->
  ModtyTail v ->
  String ->
  whn (ModtyTail v)
whnormalizeModtyTail gamma tail reason =
  case tail of
    TailEmpty -> return TailEmpty
    TailDisc   dcod -> do
      dcod <- whnormalizeMode gamma dcod reason
      case dcod of
        ReldttMode (BareMode ModeTermZero) -> return TailEmpty
        otherwise -> return $ TailDisc dcod
    TailForget ddom -> do
      ddom <- whnormalizeMode gamma ddom reason
      case ddom of
        ReldttMode (BareMode ModeTermZero) -> return TailEmpty
        otherwise -> return $ TailForget ddom
    TailDiscForget ddom dcod -> do
      ddom <- whnormalizeMode gamma ddom reason
      dcod <- whnormalizeMode gamma dcod reason
      case (ddom, dcod) of
        (ReldttMode (BareMode ModeTermZero),
         ReldttMode (BareMode ModeTermZero)) -> return TailEmpty
        (ReldttMode (BareMode ModeTermZero), _) -> return $ TailDisc dcod
        (_, ReldttMode (BareMode ModeTermZero)) -> return $ TailForget ddom
        (_, _) -> return $ TailDiscForget ddom dcod
    TailCont d -> do
      d <- whnormalizeMode gamma d reason
      case d of
        ReldttMode (BareMode ModeTermZero) -> return TailEmpty
        otherwise -> return $ TailCont d
    TailProblem -> return TailProblem

-- Why bother?
whnormalizeKnownModty :: forall whn v .
  (MonadWHN Reldtt whn, MonadWriter [Int] whn, DeBruijnLevel v) =>
  Ctx Type Reldtt v ->
  KnownModty v ->
  String ->
  whn (KnownModty v)
whnormalizeKnownModty gamma mu@(KnownModty snout tail) reason = do
  tail <- whnormalizeModtyTail gamma tail reason
  case tail of
    TailEmpty -> return $ KnownModty snout TailEmpty
    TailDisc dcod -> case dcod of
      ReldttMode (BareMode ModeTermZero) -> return $ KnownModty snout TailEmpty
      ReldttMode (BareMode (ModeTermSuc d)) ->
        whnormalizeKnownModty gamma (KnownModty (extDisc snout) $ TailDisc $ ReldttMode d) reason
      _ -> return $ KnownModty snout tail
    TailForget ddom -> case ddom of
      ReldttMode (BareMode ModeTermZero) -> return $ KnownModty snout TailEmpty
      ReldttMode (BareMode (ModeTermSuc d)) ->
        whnormalizeKnownModty gamma (KnownModty (extForget snout) $ TailForget $ ReldttMode d) reason
      _ -> return $ KnownModty snout tail
    TailDiscForget ddom dcod -> case dcod of
      ReldttMode (BareMode ModeTermZero) ->
        whnormalizeKnownModty gamma (KnownModty snout $ TailForget ddom) reason
      ReldttMode (BareMode (ModeTermSuc d)) ->
        whnormalizeKnownModty gamma (KnownModty (extDisc snout) $ TailDiscForget ddom (ReldttMode d)) reason
      _ -> case ddom of
        ReldttMode (BareMode ModeTermZero) ->
          whnormalizeKnownModty gamma (KnownModty snout $ TailDisc dcod) reason
        ReldttMode (BareMode (ModeTermSuc d)) ->
          whnormalizeKnownModty gamma (KnownModty (extForget snout) $ TailDiscForget (ReldttMode d) dcod) reason
        _ -> return $ KnownModty snout tail
    TailCont d -> case d of
      ReldttMode (BareMode ModeTermZero) -> return $ KnownModty snout TailEmpty
      ReldttMode (BareMode (ModeTermSuc dpred)) ->
        whnormalizeKnownModty gamma (KnownModty (extCont snout) $ TailCont $ ReldttMode dpred) reason
      _ -> return $ KnownModty snout tail
    TailProblem -> return $ KnownModty snout TailProblem

whnormalizeChainModty :: forall whn v .
  (MonadWHN Reldtt whn, MonadWriter [Int] whn, DeBruijnLevel v) =>
  Ctx Type Reldtt v ->
  ChainModty v ->
  String ->
  whn (ChainModty v)
whnormalizeChainModty gamma mu@(ChainModtyKnown knownMu) reason = return mu
  -- KnownModty's are aligned before relating them.
  --ChainModtyKnown <$> whnormalizeKnownModty gamma knownMu reason
whnormalizeChainModty gamma mu@(ChainModtyLink knownMu termNu chainRho) reason = return mu
  -- Since termNu is required to be neutral, this thing is already normal!
  {-do
  -- mu . nu . rho
  knownMu <- whnormalizeKnownModty gamma knownMu reason
  ------------------------------------------
  -- vv -- kind of useless, but a good guard.
  (termNu, metasTermNu) <- whnormalize gamma termNu
    (BareSysType $ SysTypeModty (_chainModty'cod chainRho) (_knownModty'dom knownMu)) reason
  let () = case metasTermNu of
    _:_ -> unreachable -- termNu must be normal in a ChainModtyLink!
    [] -> ()
  -- ^^ -- kind of useless, but a good guard
  ------------------------------------------
  case termNu of
    BareChainModty chainNu -> do
      chainNu <- whnormalizeChainModty gamma chainNu reason
      case chainNu of
        ChainModtyKnown knownNu -> do
          let composite = case chainRho of
                ChainModtyKnown knownRho ->
                  ChainModtyKnown (knownMu `compKnownModty` knownNu `compKnownModty` knownRho)
                ChainModtyLink knownSigma termTau chainUpsilon ->
                  -- mu . nu . sigma . tau . upsilon
                  ChainModtyLink (knownMu `compKnownModty` knownNu `compKnownModty` knownSigma) termTau chainUpsilon
                ChainModtyTerm ddom dcod trho ->
                  ChainModtyLink (knownMu `compKnownModty` knownNu) (BareChainModty chainRho) $
                    ChainModtyKnown $ idKnownModty ddom
          whnormalizeChainModty gamma composite reason
        ChainModtyLink knownNuA termNuB chainNuC -> do
          -- mu . nuA . nuB . nuC . rho
          let composite = ChainModtyLink (knownMu `compKnownModty` knownNuA) termNuB $
                          compMod chainNuC chainRho
          whnormalizeChainModty gamma composite reason
        ChainModtyTerm ddom dcod tnu -> return $ ChainModtyLink knownMu termNu chainRho
    _ -> return $ ChainModtyLink knownMu termNu chainRho-}
whnormalizeChainModty gamma chmu@(ChainModtyTerm dom cod tmu) reason = do
  (tmu, metasTMu) <- listen $ whnormalize gamma tmu (BareSysType $ SysTypeModty dom cod) reason
  case (tmu, metasTMu) of
    (BareChainModty chmu, []) -> whnormalizeChainModty gamma chmu reason
    (_, []) -> whnormalizeChainModty gamma
      (ChainModtyLink (idKnownModty cod) tmu $ ChainModtyKnown $ idKnownModty dom)
      reason
    otherwise -> return $ ChainModtyTerm dom cod tmu
whnormalizeChainModty gamma chmu@(ChainModtyMeta dom cod meta depcies) reason = do
  maybeSolution <- awaitMeta reason meta depcies
  case maybeSolution of
    Nothing -> chmu <$ tell [meta]
    Just solution -> whnormalizeChainModty gamma solution reason
whnormalizeChainModty gamma chmu@(ChainModtyAlreadyChecked dom cod chmuChecked) reason =
  whnormalizeChainModty gamma chmuChecked reason

{-
whnormalizeChainModty :: forall whn v .
  (MonadWHN Reldtt whn, MonadWriter [Int] whn, DeBruijnLevel v) =>
  Ctx Type Reldtt v ->
  ChainModty v ->
  String ->
  whn (ChainModty v)
whnormalizeChainModty gamma chmu reason = do
  let cod = _chainModty'cod chmu
  whnCod <- whnormalizeMode gamma cod reason
  case whnCod of
    ReldttMode (BareMode ModeTermZero) -> return $ ChainModtyKnown $
      forgetKnownModty $ _chainModty'dom chmu
    otherwise -> whnormalizeChainModtyNonzeroCod gamma chmu reason
-}

whnormalizeModeTerm :: forall whn v .
  (MonadWHN Reldtt whn, MonadWriter [Int] whn, DeBruijnLevel v) =>
  Ctx Type Reldtt v ->
  ModeTerm v ->
  String ->
  whn (ModeTerm v)
whnormalizeModeTerm gamma d reason = case d of
  ModeTermZero -> return $ ModeTermZero
  --ModeTermFinite t -> BareMode . ModeTermFinite <$> whnormalize gamma t (hs2type NatType) reason
  ModeTermSuc d -> do
    d <- whnormalize gamma d (BareSysType $ SysTypeMode) reason
    case d of
      BareMode ModeTermOmega -> return $ ModeTermOmega
      _ -> return $ ModeTermSuc d
  ModeTermOmega -> return $ ModeTermOmega

whnormalizeModtyTerm :: forall whn v .
  (MonadWHN Reldtt whn, MonadWriter [Int] whn, DeBruijnLevel v) =>
  Ctx Type Reldtt v ->
  ModtyTerm v ->
  String ->
  whn (ModtyTerm v)
whnormalizeModtyTerm gamma mu reason = case mu of
  -- ModtyTermChain is a constructor, don't normalize under it!
  ModtyTermChain chmu -> return mu
  ModtyTermDiv rho nu -> todo -- only for prettyprinting
  ModtyTermApproxLeftAdjointProj chrho -> do
    chrho <- whnormalizeChainModty gamma chrho reason
    case chrho of
      ChainModtyKnown krho -> case knownApproxLeftAdjointProj krho of
        Just kmu -> return $ ModtyTermChain $ ChainModtyKnown $ kmu
        Nothing -> return mu
      otherwise -> return mu
  ModtyTermComp chmu2 chmu1 -> do
    (chmu1, metas1) <- listen $ whnormalizeChainModty gamma chmu1 reason
    (chmu2, metas2) <- listen $ whnormalizeChainModty gamma chmu2 reason
    case (metas1, metas2) of
      ([], []) -> return $ ModtyTermChain $ chmu2 `compChainModty` chmu1
      (_, _) -> return $ ModtyTermComp chmu2 chmu1
  ModtyTermUnavailable ddom dcod -> return mu
  
whnormalizeReldttDegree :: forall whn v .
  (MonadWHN Reldtt whn, MonadWriter [Int] whn, DeBruijnLevel v) =>
  Ctx Type Reldtt v ->
  ReldttDegree v ->
  String ->
  whn (ReldttDegree v)
whnormalizeReldttDegree gamma i reason = do
    case i of
      DegKnown _ _ -> return i
      DegGet j chmu -> do
        j <- whnormalizeReldttDegree gamma j reason
        case j of
          DegKnown d KnownDegEq -> return $ DegKnown (_chainModty'dom chmu) KnownDegEq
          DegKnown d KnownDegTop -> return $ DegKnown (_chainModty'dom chmu) KnownDegTop
          DegKnown d j' -> do
            chmu <- whnormalizeChainModty gamma chmu reason
            case chmu of
              ChainModtyKnown kmu -> return $ DegKnown (_chainModty'dom chmu) $ knownGetDeg j' kmu 
              _ -> return $ DegGet j chmu
          _ -> return $ DegGet j chmu
  
instance SysWHN Reldtt where
  whnormalizeSysTerm gamma sysT ty reason = do
    --let returnSysT = return $ Expr2 $ TermSys $ sysT
    --let returnProblem = return $ Expr2 $ TermProblem $ Expr2 $ TermSys $ sysT
    case sysT of
      SysTermMode d -> BareMode <$> whnormalizeModeTerm gamma d reason
      SysTermModty mu -> BareModty <$> whnormalizeModtyTerm gamma mu reason
      -- This is a constructor, don't normalize under it!
      -- SysTermChainModtyInDisguise chmu -> return $ Expr2 $ TermSys $ sysT
{-      SysTermDeg i -> case i of
        DegKnown _ -> return $ BareDeg i
        DegGet j mu ddom dcod -> do
          j <- whnormalize gamma j (BareSysType $ SysTypeDeg dcod) reason
          case j of
            BareKnownDeg KnownDegEq -> return $ BareKnownDeg KnownDegEq
            BareKnownDeg KnownDegTop -> return $ BareKnownDeg KnownDegTop
            BareKnownDeg j' -> do
              mu <- whnormalize gamma mu (BareSysType $ SysTypeModty ddom dcod) reason
              case mu of
                BareKnownModty mu' -> return $ BareKnownDeg $ knownGetDeg j' mu' 
                _ -> return $ BareDeg $ DegGet j mu ddom dcod
            _ -> return $ BareDeg $ DegGet j mu ddom dcod-}
      --SysTypeMode -> returnSysT
      --SysTypeDeg d -> returnSysT
      --SysTypeModty ddom dcod -> returnSysT
      --_ -> _whnormalizeSys

  {-
  whnormalizeMode gamma (ReldttMode t) reason = ReldttMode !<$> whnormalize gamma t (BareSysType SysTypeMode) reason

  whnormalizeModality gamma chmu dom cod reason = whnormalizeChainModty gamma chmu reason

  whnormalizeDegree gamma i d reason = do
    case i of
      DegKnown _ _ -> return i
      DegGet j mu ddom dcod -> do
        j <- whnormalizeDegree gamma j dcod reason
        case j of
          DegKnown d KnownDegEq -> return $ DegKnown ddom KnownDegEq
          DegKnown d KnownDegTop -> return $ DegKnown ddom KnownDegTop
          DegKnown d j' -> do
            mu <- whnormalize gamma mu (BareSysType $ SysTypeModty ddom dcod) reason
            case mu of
              BareKnownModty mu' -> return $ DegKnown ddom $ knownGetDeg j' mu' 
              _ -> return $ DegGet j mu ddom dcod
          _ -> return $ DegGet j mu ddom dcod
  -}

  whnormalizeMultimodeOrSysAST token gamma t extraT classifT reason = case token of
    Left AnTokenMode -> ReldttMode !<$> whnormalize gamma (getReldttMode t) (BareSysType SysTypeMode) reason
    Left AnTokenModality -> whnormalizeChainModty gamma t reason
    Left AnTokenDegree -> whnormalizeReldttDegree gamma t reason
    Right AnTokenModeTerm -> whnormalizeModeTerm gamma t reason
    Right AnTokenModtyTerm -> whnormalizeModtyTerm gamma t reason
    Right AnTokenKnownModty -> whnormalizeKnownModty gamma t reason
    Right AnTokenModtySnout -> return t
    Right AnTokenModtyTail -> whnormalizeModtyTail gamma t reason

  leqMod gamma mu1 mu2 ddom dcod reason = do
    -- You need to normalize: a tail might become empty!
    (mu1, metasMu1) <- runWriterT $ whnormalizeChainModty gamma mu1 reason
    (mu2, metasMu2) <- runWriterT $ whnormalizeChainModty gamma mu2 reason
    case (metasMu1, metasMu2) of
      -- Both are normal
      ([], []) -> case (mu1, mu2) of
        (ChainModtyKnown kmu1, ChainModtyKnown kmu2) -> return $ Just $ fromMaybe False $ relKnownModty ModLeq kmu1 kmu2
        -- There are neutrals involved: don't bother.
        (_, _) -> return $ Just False
      -- Either is not normal
      (_ , _ ) -> return $ Nothing

  leqDeg gamma deg1 deg2 d reason = do
    (deg1, metasDeg1) <- runWriterT $ whnormalizeDegree gamma deg1 d reason
    (deg2, metasDeg2) <- runWriterT $ whnormalizeDegree gamma deg2 d reason
    case (metasDeg1, deg1, metasDeg2, deg2) of
      (_, DegKnown _ i1, _, DegKnown _ i2) -> return $ Just $ i1 <= i2
      ([], _, [], _) -> return $ Just False
      (_ , _, _ , _) -> return Nothing
