module Menkar.Systems.Reldtt.WHN where

import Menkar.Basic
import Menkar.WHN
import Menkar.System.Fine
import Menkar.System.Scoper
import Menkar.System.WHN
import Menkar.Fine
import Menkar.Monad
import Menkar.Systems.Reldtt.Fine
import Menkar.Systems.Reldtt.Scoper

import Control.Monad.DoUntilFail

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

-- | The omega-case is not really handled!
compModtySnout :: ModtySnout -> KnownModty v -> ModtySnout
compModtySnout (ModtySnout kmid kcod []) mu =
  ModtySnout (_modtySnout'dom $ _knownModty'snout $ mu) kcod []
compModtySnout (ModtySnout kmid kcod krevdegs) mu =
  ModtySnout (_modtySnout'dom $ _knownModty'snout $ mu) kcod $ flip knownGetDeg mu <$> krevdegs

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

{-
whnormalizeComp :: forall whn v .
  (MonadWHN Reldtt whn, MonadWriter [Int] whn, DeBruijnLevel v) =>
  Constraint Reldtt ->
  Ctx Type Reldtt v Void ->
  Term Reldtt v ->
  Term Reldtt v ->
  Term Reldtt v ->
  Type Reldtt v ->
  String ->
  whn (Term Reldtt v)
whnormalizeComp parent gamma mu2 dmid mu1 ty reason = do
  whnTy <- whnormalizeType parent gamma ty reason
  let giveUp = return $ BareModty $ ModtyTermComp mu2 dmid mu1
  case unType whnTy of
    Expr2 (TermSys (SysTypeModty ddom dcod)) -> do
      whnMu1 <- whnormalize parent gamma mu1 (Type $ Expr2 $ TermSys $ SysTypeModty ddom dmid) reason
      whnMu2 <- whnormalize parent gamma mu2 (Type $ Expr2 $ TermSys $ SysTypeModty dmid dcod) reason
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
  TailProblem -> KnownDegProblem
  TailCont d -> KnownDegOmega
  _ -> knownGetDeg (KnownDeg $ idom - 1) mu

---------------------

knownApproxLeftAdjointProj :: KnownModty v -> KnownModty v
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
          case remainingTail of
            nextDeg : remainingTail' -> if nextDeg <= KnownDeg threshold
              then do -- Write a degree, increase the length
                nextDeg' <- use _1
                _3 %= (nextDeg' :)
                _4 += 1
                return True
              else do -- Pop a degree, increase the pop-counter
                _2 .= remainingTail'
                _1 += 1
                return True
            [] -> do
              currentLength <- use _4
              if currentLength < idom
                then do -- Write a degree, increase the length
                  nextDeg' <- use _1
                  _3 %= (nextDeg' :)
                  _4 += 1
                  return True
                else return False
      snout' = ModtySnout icod idom (int2deg <$> krevdegs')
      snoutCohpi' = ModtySnout icod idom $ krevdegs' <&> \ i -> if i == (idom - 1) then KnownDegOmega else int2deg i
  in  case tail of
        TailEmpty -> KnownModty snout' $ TailEmpty
        TailDisc dcod -> KnownModty snoutCohpi' $ TailForget dcod
        TailForget ddom -> KnownModty snout' $ TailDisc ddom
        TailDiscForget ddom dcod -> KnownModty snoutCohpi' $ TailDiscForget dcod ddom
        TailCont d -> KnownModty snout' $ TailCont d
        TailProblem -> KnownModty snout' $ TailProblem
  where int2deg :: Int -> KnownDeg
        int2deg (-1) = KnownDegEq
        int2deg i = KnownDeg i

---------------------

whnormalizeModtyTail :: forall whn v .
  (MonadWHN Reldtt whn, MonadWriter [Int] whn, DeBruijnLevel v) =>
  Constraint Reldtt ->
  Ctx Type Reldtt v Void ->
  ModtyTail v ->
  String ->
  whn (ModtyTail v)
whnormalizeModtyTail parent gamma tail reason =
  case tail of
    TailEmpty -> return TailEmpty
    TailDisc   dcod -> TailDisc   <$> whnormalize parent gamma dcod (BareSysType $ SysTypeMode) reason
    TailForget ddom -> TailForget <$> whnormalize parent gamma ddom (BareSysType $ SysTypeMode) reason
    TailDiscForget ddom dcod -> TailDiscForget <$> whnormalize parent gamma ddom (BareSysType $ SysTypeMode) reason
                                               <*> whnormalize parent gamma dcod (BareSysType $ SysTypeMode) reason
    TailCont   d    -> TailCont   <$> whnormalize parent gamma d    (BareSysType $ SysTypeMode) reason
    TailProblem -> return TailProblem

whnormalizeKnownModty :: forall whn v .
  (MonadWHN Reldtt whn, MonadWriter [Int] whn, DeBruijnLevel v) =>
  Constraint Reldtt ->
  Ctx Type Reldtt v Void ->
  KnownModty v ->
  String ->
  whn (KnownModty v)
whnormalizeKnownModty parent gamma mu@(KnownModty snout tail) reason = do
  tail <- whnormalizeModtyTail parent gamma tail reason
  let snoutNoOmegas = numberfyOmegasForDomainlessTail snout
  case tail of
    TailEmpty -> return $ KnownModty snout TailEmpty
    TailDisc dcod -> case dcod of
      BareFinMode ConsZero -> return $ KnownModty snoutNoOmegas TailEmpty
      BareFinMode (ConsSuc d) ->
        whnormalizeKnownModty parent gamma (KnownModty (extDisc snoutNoOmegas) $ TailDisc d) reason
      _ -> return $ KnownModty snout tail
    TailForget ddom -> case ddom of
      BareFinMode ConsZero -> return $ KnownModty snoutNoOmegas TailEmpty
      BareFinMode (ConsSuc d) ->
        whnormalizeKnownModty parent gamma (KnownModty (extForget snout) $ TailForget d) reason
      _ -> return $ KnownModty snout tail
    TailDiscForget ddom dcod -> case dcod of
      BareFinMode ConsZero ->
        whnormalizeKnownModty parent gamma (KnownModty snout $ TailForget ddom) reason
      BareFinMode (ConsSuc d) ->
        whnormalizeKnownModty parent gamma (KnownModty (extDisc snout) $ TailDiscForget ddom d) reason
      _ -> case ddom of
        BareFinMode ConsZero ->
          whnormalizeKnownModty parent gamma (KnownModty snoutNoOmegas $ TailDisc dcod) reason
        BareFinMode (ConsSuc d) ->
          whnormalizeKnownModty parent gamma (KnownModty (extForget snout) $ TailDiscForget d dcod) reason
        _ -> return $ KnownModty snout tail
    TailCont d -> case d of
      BareFinMode ConsZero -> return $ KnownModty snoutNoOmegas TailEmpty
      BareFinMode (ConsSuc dpred) ->
        whnormalizeKnownModty parent gamma (KnownModty (extCont snout) $ TailCont dpred) reason
      _ -> return $ KnownModty snout tail
    TailProblem -> return $ KnownModty snout TailProblem

whnormalizeChainModty :: forall whn v .
  (MonadWHN Reldtt whn, MonadWriter [Int] whn, DeBruijnLevel v) =>
  Constraint Reldtt ->
  Ctx Type Reldtt v Void ->
  ChainModty v ->
  String ->
  whn (ChainModty v)
whnormalizeChainModty parent gamma mu@(ChainModty knownMu remainder) reason = do
  knownMu <- whnormalizeKnownModty parent gamma knownMu reason
  -- mu . remainder
  case (getCompose remainder) of
    -- mu
    [] -> return $ ChainModtyKnown knownMu
    -- mu . nu . rho . remainderTail
    (termNu :*: knownRho) : remainderTail -> do
      termNu <- whnormalize parent gamma termNu
        (BareSysType $ SysTypeModty (_knownModty'cod knownRho) (_knownModty'dom knownMu)) reason
      case termNu of
        BareChainModty chainNu -> case chainNu of
          -- mu . nu . rho . remainderTail
          ChainModty knownNu (Compose []) ->
            whnormalizeChainModty parent gamma
              (ChainModty (knownMu `compKnownModty` knownNu `compKnownModty` knownRho) $ Compose remainderTail)
              reason
          -- mu . nu1 . remainderNu . rho . remainderTail
          ChainModty knownNu1 (Compose remainderNu) -> do
            -- mu . nu1 . init remainderNu . phi . chi . rho . remainderTail
            let (termPhi :*: knownChi) = last remainderNu
            -- mu . nu1 . init remainderNu . fuser . remainderTail
            let fuser = (termPhi :*: knownChi `compKnownModty` knownRho)
            -- mu . nu1 . newRemainder
            let newRemainder = init remainderNu ++ (fuser : remainderTail)
            whnormalizeChainModty parent gamma
              (ChainModty (knownMu `compKnownModty` knownNu1) $ Compose $ newRemainder)
              reason
        _ -> return $ ChainModty knownMu $ Compose $ (termNu :*: knownRho) : remainderTail

instance SysWHN Reldtt where
  whnormalizeSys parent gamma sysT ty reason = do
    let returnSysT = return $ Expr2 $ TermSys $ sysT
    --let returnProblem = return $ Expr2 $ TermProblem $ Expr2 $ TermSys $ sysT
    case sysT of
      SysTermMode d -> case d of
        ModeTermFinite t -> BareMode . ModeTermFinite <$> whnormalize parent gamma t (hs2type NatType) reason
        ModeTermOmega -> return $ BareMode $ ModeTermOmega
      SysTermModty mu -> case mu of
        ModtyTermChain mu -> BareChainModty <$> whnormalizeChainModty parent gamma mu reason
        ModtyTermDiv rho mu -> returnSysT -- TODO
        ModtyTermApproxLeftAdjointProj ddom dcod mu -> do
          mu <- whnormalize parent gamma mu (BareSysType $ SysTypeModty dcod ddom) reason
          case mu of
            BareKnownModty kmu ->
                 return $ BareKnownModty $ knownApproxLeftAdjointProj kmu
            _ -> return $ BareModty $ ModtyTermApproxLeftAdjointProj ddom dcod mu
        ModtyTermUnavailable ddom dcod -> returnSysT
      SysTermDeg i -> case i of
        DegKnown _ -> return $ BareDeg i
        DegGet j mu ddom dcod -> do
          j <- whnormalize parent gamma j (BareSysType $ SysTypeDeg dcod) reason
          case j of
            BareKnownDeg KnownDegEq -> return $ BareKnownDeg KnownDegEq
            BareKnownDeg KnownDegTop -> return $ BareKnownDeg KnownDegTop
            BareKnownDeg j' -> do
              mu <- whnormalize parent gamma mu (BareSysType $ SysTypeModty ddom dcod) reason
              case mu of
                BareKnownModty mu' -> return $ BareKnownDeg $ knownGetDeg j' mu' 
                _ -> return $ BareDeg $ DegGet j mu ddom dcod
            _ -> return $ BareDeg $ DegGet j mu ddom dcod
      --SysTypeMode -> returnSysT
      --SysTypeDeg d -> returnSysT
      --SysTypeModty ddom dcod -> returnSysT
      --_ -> _whnormalizeSys

  leqMod parent gamma mu1 mu2 ddom dcod reason = runMaybeT $ do
    -- You need to normalize: a tail might become empty!
    (mu1, metasMu1) <- lift $ runWriterT $ whnormalizeChainModty parent gamma mu1 reason
    (mu2, metasMu2) <- lift $ runWriterT $ whnormalizeChainModty parent gamma mu2 reason
    case (metasMu1, metasMu2) of
      -- Both are normal
      ([], []) -> case (mu1, mu2) of
        (ChainModtyKnown kmu1@(KnownModty snout1 tail1), ChainModtyKnown kmu2@(KnownModty snout2 tail2)) -> do
          (kmu1, kmu2) <- MaybeT $ return $
            case compare (_modtySnout'dom $ _knownModty'snout kmu1) (_modtySnout'dom $ _knownModty'snout kmu2) of
              LT -> (, kmu2) <$> forceDom snout1 tail1 (_modtySnout'dom snout2) (_modtyTail'dom tail2)
              EQ -> Just (kmu1, kmu2)
              GT -> (kmu1, ) <$> forceDom snout2 tail2 (_modtySnout'dom snout1) (_modtyTail'dom tail1)
          (kmu1, kmu2) <- MaybeT $ return $
            case compare (_modtySnout'cod $ _knownModty'snout kmu1) (_modtySnout'cod $ _knownModty'snout kmu2) of
              LT -> (, kmu2) <$> forceCod snout1 tail1 (_modtySnout'cod snout2) (_modtyTail'cod tail2)
              EQ -> Just (kmu1, kmu2)
              GT -> (kmu1, ) <$> forceCod snout2 tail2 (_modtySnout'cod snout1) (_modtyTail'cod tail1)
          let leqSnout = and $ getZipList $
                (<=) <$> ZipList (_modtySnout'degreesReversed $ _knownModty'snout kmu1)
                     <*> ZipList (_modtySnout'degreesReversed $ _knownModty'snout kmu2)
          return $ leqSnout && leqTail kmu1 kmu2
        -- There are neutrals involved: don't bother.
        (_, _) -> return False
      -- Either is not normal
      (_ , _ ) -> MaybeT $ return $ Nothing

  leqDeg parent gamma deg1 deg2 d reason = do
    (deg1, metasDeg1) <- runWriterT $ whnormalize parent gamma deg1 (BareSysType $ SysTypeDeg d) reason
    (deg2, metasDeg2) <- runWriterT $ whnormalize parent gamma deg2 (BareSysType $ SysTypeDeg d) reason
    case (metasDeg1, deg1, metasDeg2, deg2) of
      (_, BareKnownDeg i1, _, BareKnownDeg i2) -> return $ Just $ i1 <= i2
      ([], _, [], _) -> return $ Just False
      (_ , _, _ , _) -> return Nothing
