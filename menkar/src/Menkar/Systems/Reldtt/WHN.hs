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

import Control.Monad.Writer.Class
import Data.Void

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
          --purposefully shadowing
          (snout1, snout2) <- case compare (_knownModty'cod snout1) (_knownModty'dom snout2) of
            LT -> _
            EQ -> return (snout1, snout2)
            GT -> _
          _
        (_, _) -> return $ BareModty $ ModtyTermComp whnMu2 dmid whnMu1
    otherwise -> giveUp

{-
whnormalizeModty :: forall whn v .
  (MonadWHN Reldtt whn, MonadWriter [Int] whn, DeBruijnLevel v) =>
  Constraint Reldtt ->
  Ctx Type Reldtt v Void ->
  ModtyTerm v ->
  Type Reldtt v ->
  String ->
  whn (ReldttModality v)
whnormalizeModty parent gamma mu ty reason = do
  let returnMu = return $ BareModty $ mu
  --let returnMuProblem = return $ ReldttModality $ Expr2 $ TermProblem $ Expr2 $ TermSys $ TermModty $ mu
  case mu of
    ModtyTermCrisp ddom dcod -> returnMu
    ModtyTermDiscPar d m n -> do
      whnD <- whnormalize parent gamma d (hs2type NatType) reason
      case whnD of
        Expr2 (TermCons ConsZero) -> return $ BareModty $ ModtyTermCrisp m n
        _ -> returnMu
    ModtyTermDiscIrr ddom d n -> do
      whnD <- whnormalize parent gamma d (hs2type NatType) reason
      case whnD of
        Expr2 (TermCons ConsZero) -> return $ BareModty $ ModtyTermCrisp ddom n
        _ -> returnMu

    ModtyTermCrispOne dcod -> returnMu
    ModtyTermDiscRelOne d n -> do
      whnD <- whnormalize parent gamma d (hs2type NatType) reason
      case whnD of
        Expr2 (TermCons ConsZero) -> return $ BareModty $ ModtyTermCrispOne n
        _ -> returnMu
    ModtyTermDiscIrrOne d n -> do
      whnD <- whnormalize parent gamma d (hs2type NatType) reason
      case whnD of
        Expr2 (TermCons ConsZero) -> return $ BareModty $ ModtyTermCrispOne n
        _ -> returnMu

    ModtyTermCrispOneOne -> returnMu
    ModtyTermContOneOne -> returnMu
    ModtyTermIrrOneOne -> returnMu

    ModtyTermCrispNull dcod -> returnMu
    ModtyTermDiscIrrNull d n -> do
      whnD <- whnormalize parent gamma d (hs2type NatType) reason
      case whnD of
        Expr2 (TermCons ConsZero) -> return $ BareModty $ ModtyTermCrispNull n
        _ -> returnMu
        
    ModtyTermCrispNullOne -> returnMu
    ModtyTermIrrNullOne -> returnMu
    
    ModtyTermNullNull -> returnMu

    ModtyTermComp mu2 dmid mu1 -> whnormalizeComp parent gamma mu2 dmid mu1 reason
    ModtyTermDiv rho mu -> returnMu -- TODO
    ModtyApproxLeftAdjointProj mu -> _ModtyApproxLeftAdjointProj

instance SysWHN Reldtt where
  whnormalizeSys parent gamma (TermModty mu) ty reason =
    unModality <$> whnormalizeModty parent gamma mu ty reason
  whnormalizeSys parent gamma t ty reason = _whnormalizeSys

  leqMod ddom dcod mu1 mu2 = _leqMod

  leqDeg d deg1 deg2 = _leqDeg
    
-}

instance SysWHN Reldtt where
  whnormalizeSys parent gamma sysT ty reason = do
    let returnSysT = return $ Expr2 $ TermSys $ sysT
    --let returnProblem = return $ Expr2 $ TermProblem $ Expr2 $ TermSys $ sysT
    case sysT of
      SysTermMode d -> case d of
        ModeTermFinite t -> BareMode . ModeTermFinite <$> whnormalize parent gamma t (hs2type NatType) reason
        ModeTermOmega -> return $ BareMode $ ModeTermOmega
      SysTermModty mu -> case mu of
        ModtyTerm knownPart tail -> returnSysT
          {-
          TailEmpty -> returnSysT
          TailDisc dcod -> do
            whnDCod <- whnormalize parent gamma dcod (Expr2 $ TermSys $ SysTypeMode) reason
            case whnDCod of
              BareFinMode ConsZero -> return $ BareModty $ ModtyTerm knownPart TailEmpty
              BareFinMode (ConsSuc d) ->
                whnormalize parent gamma (BareModty $ ModtyTerm (extDisc knownPart) $ TailDisc d) ty reason
              _ -> return $ BareModty $ ModtyTerm knownPart $ TailDisc whnDCod
          TailCodisc dcod -> do
            whnDCod <- whnormalize parent gamma dcod (Expr2 $ TermSys $ SysTypeMode) reason
            case whnDCod of
              BareFinMode ConsZero -> return $ BareModty $ ModtyTerm knownPart TailEmpty
              BareFinMode (ConsSuc d) ->
                whnormalize parent gamma (BareModty $ ModtyTerm (extCodisc knownPart) $ TailCodisc d) ty reason
              _ -> return $ BareModty $ ModtyTerm knownPart $ TailCodisc whnDCod
          TailForget ddom -> do
            whnDDom <- whnormalize parent gamma ddom (Expr2 $ TermSys $ SysTypeMode) reason
            case whnDDom of
              BareFinMode ConsZero -> return $ BareModty $ ModtyTerm knownPart TailEmpty
              BareFinMode (ConsSuc d) ->
                whnormalize parent gamma (BareModty $ ModtyTerm (extForget knownPart) $ TailForget d) ty reason
              _ -> return $ BareModty $ ModtyTerm knownPart $ TailForget whnDDom
          TailDiscForget ddom dcod -> do
            whnDCod <- whnormalize parent gamma dcod (Expr2 $ TermSys $ SysTypeMode) reason
            case whnDCod of
              BareFinMode ConsZero ->
                whnormalize parent gamma (BareModty $ ModtyTerm knownPart $ TailForget ddom) ty reason
              BareFinMode (ConsSuc d) ->
                whnormalize parent gamma (BareModty $ ModtyTerm (extDisc knownPart) $ TailDiscForget ddom d) ty reason
              _ -> do
                whnDDom <- whnormalize parent gamma ddom (Expr2 $ TermSys $ SysTypeMode) reason
                case whnDDom of
                  BareFinMode ConsZero ->
                    whnormalize parent gamma (BareModty $ ModtyTerm knownPart $ TailDisc whnDCod) ty reason
                  BareFinMode (ConsSuc d)
          _ -> _whnormalizeModty'
          -}
        ModtyTermComp mu2 dmid mu1 -> whnormalizeComp parent gamma mu2 dmid mu1 ty reason
        ModtyTermDiv rho mu -> returnSysT -- TODO
        ModtyTermApproxLeftAdjointProj mu -> _ModtyApproxLeftAdjointProj
        ModtyTermUnavailable ddom dcod -> returnSysT
      _ -> _whnormalizeSys

  leqMod ddom dcod mu1 mu2 = _leqMod

  leqDeg d deg1 deg2 = _leqDeg
