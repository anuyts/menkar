{-# LANGUAGE IncoherentInstances #-}

module Menkar.TC.Inference.Solve where

import Menkar.Fine.Syntax
import Menkar.Basic.Context
import Menkar.Fine.Context
import Menkar.Fine.Judgement
import Menkar.Fine.Multimode
import Menkar.Fine.LookupQName
import qualified Menkar.Raw.Syntax as Raw
import Menkar.TC.Monad
import Control.Exception.AssertFalse
import Menkar.Fine.WHNormalize

import Data.Void
import Control.Lens
import Data.Functor.Compose
import Control.Monad
import Control.Monad.Writer.Lazy
import Data.List
import Data.List.Unique
import Data.Proxy

checkMetaPure :: (MonadTC mode modty rel tc, Eq v, DeBruijnLevel v) =>
  Constraint mode modty rel ->
  Ctx Type mode modty vOrig Void ->
  Ctx Type mode modty v Void ->
  (vOrig -> v) ->
  Type mode modty v ->
  tc Bool
checkMetaPure parent gamma depcyVars ty = _checkMetaPure

------------------------------------

whsolveMeta :: (MonadTC mode modty rel tc, Eq v, DeBruijnLevel v) =>
  Constraint mode modty rel ->
  rel v ->
  Ctx (Pair3 Type) mode modty v Void ->
  Int ->
  [v] ->
  Type mode modty v ->
  Term mode modty v ->
  Type mode modty v ->
  tc (Maybe (Term mode modty v))
whsolveMeta parent deg gamma meta depcyVars tyMeta tSolution tySolution = _whsolveMeta

------------------------------------

tryToWHSolveMeta :: (MonadTC mode modty rel tc, Eq v, DeBruijnLevel v) =>
  Constraint mode modty rel ->
  rel v ->
  Ctx (Pair3 Type) mode modty v Void ->
  Int ->
  [Term mode modty v] ->
  Type mode modty v ->
  Term mode modty v ->
  Type mode modty v ->
  tc ()
tryToWHSolveMeta parent deg gamma meta depcies tyMeta tSolution tySolution = do
  let getVar3 :: Term mode modty v -> Maybe v
      getVar3 (Var3 v) = Just v
      getVar3 _ = Nothing
  case sequenceA $ getVar3 <$> depcies of
    -- Some dependency is not a variable
    Nothing -> blockOnMetas [meta] parent
    -- All dependencies are variables
    Just depcyVars -> do
      let (_, repeatedVars, _) = complex depcyVars
      case repeatedVars of
        -- All variables are unique
        [] -> solveMeta meta ( \ gammaOrig -> do
            -- Turn list of variables into a function mapping variables from gammaOrig to variables from gamma
            let depcySubst = (depcyVars !!) . fromIntegral . (getDeBruijnLevel Proxy)
            -- Check if the meta is pure
            isPure <- checkMetaPure parent gammaOrig (fstCtx gamma) depcySubst tyMeta
            if isPure
              -- If so, weak-head-solve it
              then do
                -- NOTE: YOU SHOULD WHSOLVE USING VARIABLES FROM GAMMAORIG, NOT FROM GAMMA
                let depcySubstInv = _depcySubstInv
                      --(fmap $ forDeBruijnLevel Proxy) . fmap fromIntegral . (flip elemIndex depcyVars)
                solution <- whsolveMeta parent deg gamma meta depcyVars tyMeta tSolution tySolution
                return $ _ solution
              -- otherwise, block and fail to solve it (we need to give a return value to solveMeta).
              else do
                blockOnMetas [meta] parent
                return Nothing
          )
        -- Some variables occur twice
        _ -> blockOnMetas [meta] parent

tryToWHSolveTerm :: (MonadTC mode modty rel tc, Eq v, DeBruijnLevel v) =>
  Constraint mode modty rel ->
  rel v ->
  Ctx (Pair3 Type) mode modty v Void ->
  Term mode modty v ->
  Term mode modty v ->
  [Int] ->
  Type mode modty v ->
  Type mode modty v ->
  tc ()
tryToWHSolveTerm parent deg gamma tBlocked tSolution metasBlocked tyBlocked tySolution = case tBlocked of
  -- tBlocked should be a meta
  (Expr3 (TermMeta meta depcies)) ->
    tryToWHSolveMeta parent deg gamma meta (getCompose depcies) tyBlocked tSolution tySolution
  -- if tBlocked is not a meta, then we should just block on its submetas
  _ -> blockOnMetas metasBlocked parent
