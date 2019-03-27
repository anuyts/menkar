module Menkar.Systems.Reldtt.WHN where

import Menkar.Basic
import Menkar.System.Fine
import Menkar.System.Scoper
import Menkar.System.WHN
import Menkar.Fine
import Menkar.Monad
import Menkar.Systems.Reldtt.Fine
import Menkar.Systems.Reldtt.Scoper

import Control.Monad.Writer.Class
import Data.Void

whnormalizeModty :: (MonadWHN Reldtt m, MonadWriter [Int] m) =>
  Constraint Reldtt ->
  Ctx Type Reldtt v Void ->
  ModtyTerm v ->
  String ->
  m (ModtyTerm v)
whnormalizeModty parent gamma mu reason = do
  case mu of
    ModtyTermFinal ddom -> return $ ModtyTermFinal ddom
    ModtyTermId d -> do
      let mu' = ModtyAbs d d $ NamedBinding (Just $ Name NonOp "i") $ Var2 VarLast
      whnormalizeModty parent gamma mu' reason
    ModtyTermComp nu dmid mu -> do
      let mu' = ModtyAbs ddom dcod $ NamedBinding (Just $ Name NonOp "i") $ unDegree $
                  BareDeg $ DegGet (BareDeg $ DegGet (ReldttDegree $ Var2 VarLast) $ VarWkn <$> mu) $ VarWkn <$> nu
      whnormalizeModty parent gamma mu' reason
    _ -> _whnormalizeModty

instance SysWHN Reldtt where
  whnormalizeSys parent gamma (TermModty mu) ty reason =
    Expr2 . TermSys . TermModty <$> whnormalizeModty parent gamma mu reason
  whnormalizeSys parent gamma t ty reason = _whnormalizeSys

  leqMod ddom dcod mu1 mu2 = _leqMod

  leqDeg d deg1 deg2 = _leqDeg
    
