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

{-
forceSolveMeta :: (MonadTC mode modty rel tc, Eq v, DeBruijnLevel v, Traversable t) =>
  Constraint mode modty rel ->
  rel v ->
  Ctx Type mode modty vOrig Void ->
  Ctx (Pair3 Type) mode modty v Void ->
  (vOrig -> v) ->
  (v -> Maybe vOrig) ->
  Int ->
  Type mode modty v ->
  t v ->
  tc (Maybe (t vOrig))
forceSovleMeta parent deg gammaOrig gamma subst partialInv meta tyMeta t = do
  let maybeTOrig = sequenceA $ partialInv <$> t
  case maybeTOrig of
    
-}

newRelatedMetaTerm :: (MonadTC mode modty rel tc, Eq v, DeBruijnLevel v) =>
  Constraint mode modty rel ->
  rel v ->
  Ctx Type mode modty vOrig Void ->
  Ctx (Pair3 Type) mode modty v Void ->
  (vOrig -> v) ->
  (v -> Maybe vOrig) ->
  Term mode modty v ->
  Type mode modty v ->
  Type mode modty v ->
  String ->
  tc (Term mode modty vOrig)
newRelatedMetaTerm parent deg gammaOrig gamma subst partialInv t2 ty1 ty2 reason = do
  let maybeDegOrig = sequenceA $ partialInv <$> deg
  case maybeDegOrig of
    Nothing -> tcBlock
    Just degOrig -> do
      t1Orig <- newMetaTermNoCheck (Just parent) degOrig gammaOrig reason
      let t1 = subst <$> t1Orig
      addNewConstraint
        (JudTermRel deg gamma (Pair3 t1 t2) (Pair3 ty1 ty2))
        (Just parent)
        reason
      return t1Orig

solveMetaAgainstSegment :: (MonadTC mode modty rel tc, Eq v, DeBruijnLevel v) =>
  Constraint mode modty rel ->
  rel v ->
  Ctx Type mode modty vOrig Void ->
  Ctx (Pair3 Type) mode modty v Void ->
  (vOrig -> v) ->
  (v -> Maybe vOrig) ->
  Int ->
  Type mode modty v ->
  Segment Type mode modty v ->
  tc (Maybe (Segment Type mode modty vOrig))
solveMetaAgainstSegment parent deg gammaOrig gamma subst partialInv meta tyMeta segment = do
  _solveMetaAgainstSegment
  let modtyInOrig = sequenceA $ partialInv <$> _decl'modty segment
  return $ Just $ Declaration
    (_decl'name segment)
    _modty'
    plicity'
    ty'

solveMetaAgainstBinding :: (MonadTC mode modty rel tc, Eq v, DeBruijnLevel v) =>
  Constraint mode modty rel ->
  rel v ->
  Ctx Type mode modty vOrig Void ->
  Ctx (Pair3 Type) mode modty v Void ->
  (vOrig -> v) ->
  (v -> Maybe vOrig) ->
  Int ->
  Type mode modty v ->
  Binding Type Term mode modty v ->
  tc (Maybe (Binding Type Term mode modty vOrig))
solveMetaAgainstBinding parent deg gammaOrig gamma subst partialInv meta tyMeta binding = do
  segment' <- solveMetaAgainstSegment parent deg gammaOrig gamma subst partialInv meta tyMeta (binding'segment binding)
  _solveMetaAgainstBinding

solveMetaAgainstUniHSConstructor :: (MonadTC mode modty rel tc, Eq v, DeBruijnLevel v) =>
  Constraint mode modty rel ->
  rel v ->
  Ctx Type mode modty vOrig Void ->
  Ctx (Pair3 Type) mode modty v Void ->
  (vOrig -> v) ->
  (v -> Maybe vOrig) ->
  Int ->
  Type mode modty v ->
  UniHSConstructor mode modty v ->
  Type mode modty v ->
  tc (Maybe (UniHSConstructor mode modty vOrig))
solveMetaAgainstUniHSConstructor parent deg gammaOrig gamma subst partialInv meta tyMeta tSolution tySolution =
  case tSolution of
    UniHS d2 lvl2 -> do
      let nat = Type $ Expr3 $ TermCons $ ConsUniHS $ NatType
      lvl1Orig <- newRelatedMetaTerm parent topDeg gammaOrig gamma subst partialInv lvl2 nat nat "Inferring level."
                --newMetaTermNoCheck (Just parent) topDeg gammaOrig nat "Inferring level."
      let d1Orig = unVarFromCtx <$> ctx'mode gammaOrig
      return $ Just $ UniHS d1Orig lvl1Orig
    Pi binding -> do
      result <- solveMetaAgainstBinding parent deg gammaOrig gamma subst partialInv meta tyMeta binding
      return $ Pi <$> result
    Sigma binding -> do
      result <- solveMetaAgainstBinding parent deg gammaOrig gamma subst partialInv meta tyMeta binding
      return $ Sigma <$> result
    _ -> _solveMetaAgainstUniHSConstructor

solveMetaAgainstConstructorTerm :: (MonadTC mode modty rel tc, Eq v, DeBruijnLevel v) =>
  Constraint mode modty rel ->
  rel v ->
  Ctx Type mode modty vOrig Void ->
  Ctx (Pair3 Type) mode modty v Void ->
  (vOrig -> v) ->
  (v -> Maybe vOrig) ->
  Int ->
  Type mode modty v ->
  ConstructorTerm mode modty v ->
  Type mode modty v ->
  tc (Maybe (ConstructorTerm mode modty vOrig))
solveMetaAgainstConstructorTerm parent deg gammaOrig gamma subst partialInv meta tyMeta tSolution tySolution =
  case tSolution of
    ConsUniHS c -> do
      result <- solveMetaAgainstUniHSConstructor parent deg gammaOrig gamma subst partialInv meta tyMeta c tySolution
      return $ ConsUniHS <$> result
    _ -> _solveMetaAgainstConstructorTerm

{-| Precondition: @partialInv . subst = Just@.
-}
solveMetaAgainstWHNF :: (MonadTC mode modty rel tc, Eq v, DeBruijnLevel v) =>
  Constraint mode modty rel ->
  rel v ->
  Ctx Type mode modty vOrig Void ->
  Ctx (Pair3 Type) mode modty v Void ->
  (vOrig -> v) ->
  (v -> Maybe vOrig) ->
  Int ->
  Type mode modty v ->
  Term mode modty v ->
  Type mode modty v ->
  tc (Maybe (Term mode modty vOrig))
solveMetaAgainstWHNF parent deg gammaOrig gamma subst partialInv meta tyMeta tSolution tySolution =
  -- CMOD if deg = eqDeg and tSolution does not mention any additional variables, solve fully.
  -- Otherwise, we do a weak-head solve.
  case tSolution of
    Var3 v -> case partialInv v of
      Nothing -> do
        blockOnMetas [meta] parent
        return Nothing
      Just u -> return $ Just $ Var3 u
    Expr3 tSolution -> case tSolution of
      TermCons c -> do
        result <- solveMetaAgainstConstructorTerm parent deg gammaOrig gamma subst partialInv meta tyMeta c tySolution
        return $ Expr3 . TermCons <$> result
      --TermElim
      TermMeta _ _ -> unreachable
      TermWildcard -> unreachable
      TermQName _ _ -> unreachable
      TermSmartElim _ _ _ -> unreachable
      TermGoal _ _ -> unreachable
      TermProblem _ -> do
        tcFail parent "Nonsensical term."
        return Nothing
      _ -> _solveMetaAgainstWHNF

------------------------------------

{-| A meta is pure if it has undergone a substitution that can be inverted in the following sense:
    All variables have been substituted with variables - all different - and the inverse substitution is well-typed.

    This method returns @'Nothing'@ if the meta is pure, @'Just' (meta:metas)@ if it is presently unclear but may
    become clear if one of the listed metas is resolved, and @'Just' []@ if it is certainly false.
-}
checkMetaPure :: (MonadTC mode modty rel tc, Eq v, DeBruijnLevel v) =>
  Constraint mode modty rel ->
  Ctx Type mode modty vOrig Void ->
  Ctx Type mode modty v Void ->
  (vOrig -> v) ->
  Type mode modty v ->
  tc (Maybe [Int])
checkMetaPure parent gammaOrig gamma subst ty = do
  --let proxyOrig = ctx'sizeProxy gammaOrig
  --let proxy     = ctx'sizeProxy gamma
  --let varsOrig = listAll proxyOrig
  --let vars     = listAll proxy
  let ldivSegmentOrig u = unVarFromCtx <$> lookupVar gammaOrig u
  let ldivSegment     v = unVarFromCtx <$> lookupVar gamma     v
  let dmuOrig u = divModedModality
                    (_leftDivided'modality $ ldivSegmentOrig u)
                    (_segment'modty $ _leftDivided'content $ ldivSegmentOrig u)
  let dmu     v = divModedModality
                    (_leftDivided'modality $ ldivSegment v)
                    (_segment'modty $ _leftDivided'content $ ldivSegment v)
  -- CMODE require that forall u . dmuOrig u <= dmu (subst u)
  -- If this is false, return Just []
  -- If this is true, return Nothing
  -- If this is unclear, return some metas
  return Nothing

------------------------------------

tryToSolveMeta :: (MonadTC mode modty rel tc, Eq v, DeBruijnLevel v) =>
  Constraint mode modty rel ->
  rel v ->
  Ctx (Pair3 Type) mode modty v Void ->
  Int ->
  [Term mode modty v] ->
  Type mode modty v ->
  Term mode modty v ->
  Type mode modty v ->
  tc ()
tryToSolveMeta parent deg gamma meta depcies tyMeta tSolution tySolution = do
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
            case isPure of
              -- If so, weak-head-solve it
              Nothing -> do
                let depcySubstInv = join . fmap (forDeBruijnLevel Proxy . fromIntegral) . flip elemIndex depcyVars
                solveMetaAgainstWHNF parent deg gammaOrig gamma depcySubst depcySubstInv meta tyMeta tSolution tySolution
              -- otherwise, block and fail to solve it (we need to give a return value to solveMeta).
              Just metas -> do
                blockOnMetas (meta : metas) parent
                return Nothing
          )
        -- Some variables occur twice
        _ -> blockOnMetas [meta] parent

tryToSolveTerm :: (MonadTC mode modty rel tc, Eq v, DeBruijnLevel v) =>
  Constraint mode modty rel ->
  rel v ->
  Ctx (Pair3 Type) mode modty v Void ->
  Term mode modty v ->
  Term mode modty v ->
  [Int] ->
  Type mode modty v ->
  Type mode modty v ->
  tc ()
tryToSolveTerm parent deg gamma tBlocked tSolution metasBlocked tyBlocked tySolution = case tBlocked of
  -- tBlocked should be a meta
  (Expr3 (TermMeta meta depcies)) ->
    tryToSolveMeta parent deg gamma meta (getCompose depcies) tyBlocked tSolution tySolution
  -- if tBlocked is not a meta, then we should just block on its submetas
  _ -> blockOnMetas metasBlocked parent
