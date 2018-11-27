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
import Data.List.Unique

tryToWHSolveMeta :: (MonadTC mode modty rel tc, Eq v) =>
  Constraint mode modty rel ->
  rel v ->
  Ctx (Pair3 Type) mode modty v Void ->
  Int ->
  [Term mode modty v] ->
  Type mode modty v ->
  Term mode modty v ->
  Type mode modty v ->
  tc () ->
  tc ()
tryToWHSolveMeta parent deg gamma meta depcies tyMeta tSolution tySolution giveUp = do
  let getVar3 :: Term mode modty v -> Maybe v
      getVar3 (Var3 v) = Just v
      getVar3 _ = Nothing
  case sequenceA $ getVar3 <$> depcies of
    -- Some dependency is not a variable
    Nothing -> giveUp
    -- All dependencies are variables
    Just depcyVars -> do
      let (_, repeatedVars, _) = complex depcyVars
      case repeatedVars of
        -- All variables are unique
        [] -> _tryToWHSolveMeta
        -- Some variables occur twice
        _ -> giveUp

tryToWHSolveTerm :: (MonadTC mode modty rel tc, Eq v) =>
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
    tryToWHSolveMeta parent deg gamma meta (getCompose depcies) tyBlocked tSolution tySolution $
      blockOnMetas metasBlocked parent
  -- if tBlocked is not a meta, then we should just block on its submetas
  _ -> blockOnMetas metasBlocked parent
