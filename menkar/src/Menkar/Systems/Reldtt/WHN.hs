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

{-
whnormalizeComp :: forall whn v .
  (MonadWHN Reldtt whn, MonadWriter [Int] whn, DeBruijnLevel v) =>
  Constraint Reldtt ->
  Ctx Type Reldtt v Void ->
  ReldttModality v ->
  ReldttMode v ->
  ReldttModality v ->
  String ->
  whn (ReldttModality v)
whnormalizeComp parent gamma mu2 dmid mu1 reason = do
  _

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
        ModtyTerm knownPart tail -> case tail of
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
        _ -> _whnormalizeModty
      _ -> _whnormalizeSys

  leqMod ddom dcod mu1 mu2 = _leqMod

  leqDeg d deg1 deg2 = _leqDeg
