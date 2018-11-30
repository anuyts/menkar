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
import Data.Maybe

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

newRelatedTermMeta :: (MonadTC mode modty rel tc, Eq v, DeBruijnLevel v) =>
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
newRelatedTermMeta parent deg gammaOrig gamma subst partialInv t2 ty1 ty2 reason = do
  let maybeDegOrig = sequenceA $ partialInv <$> deg
  case maybeDegOrig of
    Nothing -> tcBlock
    Just degOrig -> do
      t1orig <- newMetaTermNoCheck (Just parent) degOrig gammaOrig reason
      let t1 = subst <$> t1orig
      addNewConstraint
        (JudTermRel deg gamma (Pair3 t1 t2) (Pair3 ty1 ty2))
        (Just parent)
        reason
      return t1orig

newRelatedTypeMeta :: (MonadTC mode modty rel tc, Eq v, DeBruijnLevel v) =>
  Constraint mode modty rel ->
  rel v ->
  Ctx Type mode modty vOrig Void ->
  Ctx (Pair3 Type) mode modty v Void ->
  (vOrig -> v) ->
  (v -> Maybe vOrig) ->
  Type mode modty v ->
  String ->
  tc (Type mode modty vOrig)
newRelatedTypeMeta parent deg gammaOrig gamma subst partialInv ty2 reason = do
  let maybeDegOrig = sequenceA $ partialInv <$> deg
  case maybeDegOrig of
    Nothing -> tcBlock
    Just degOrig -> do
      ty1orig <- Type <$> newMetaTermNoCheck (Just parent) degOrig gammaOrig reason
      let ty1 = subst <$> ty1orig
      addNewConstraint
        (JudTypeRel deg gamma (Pair3 ty1 ty2))
        (Just parent)
        reason
      return ty1orig

--------------------------

solveMetaAgainstSegment :: (MonadTC mode modty rel tc, Eq v, DeBruijnLevel v) =>
  Constraint mode modty rel ->
  rel v ->
  Ctx Type mode modty vOrig Void ->
  Ctx (Pair3 Type) mode modty v Void ->
  (vOrig -> v) ->
  (v -> Maybe vOrig) ->
  Segment Type mode modty v ->
  tc (Segment Type mode modty vOrig)
solveMetaAgainstSegment parent deg gammaOrig gamma subst partialInv segment2 = do
  let dmu2 = _decl'modty segment2
  -- CMODE: dmu1orig <- newRelatedModedModality dmu2 
  let dmu1orig = wildModedModality
  let dmu1 = subst <$> dmu1orig
  let ty2 = _decl'content segment2
  ty1orig <- newRelatedTypeMeta
               parent
               (divDeg dmu1 deg)
               (VarFromCtx <$> dmu1orig :\\ gammaOrig)
               (VarFromCtx <$> dmu2 :\\ gamma)
               subst
               partialInv
               ty2
               "Inferring segment type."
  -- CMODE: plicity
  return $ Declaration
    (_decl'name segment2)
    dmu1orig
    (fromMaybe Explicit $ sequenceA $ partialInv <$> _decl'plicity segment2)
    ty1orig

solveMetaAgainstBinding :: (MonadTC mode modty rel tc, Eq v, DeBruijnLevel v) =>
  Constraint mode modty rel ->
  rel v ->
  Ctx Type mode modty vOrig Void ->
  Ctx (Pair3 Type) mode modty v Void ->
  (vOrig -> v) ->
  (v -> Maybe vOrig) ->
  Type mode modty (VarExt v) ->
  Type mode modty (VarExt v) ->
  Binding Type Term mode modty v ->
  tc (Binding Type Term mode modty vOrig)
solveMetaAgainstBinding parent deg gammaOrig gamma subst partialInv tyBody1 tyBody2 binding2 = do
  let segment2 = binding'segment binding2
  segment1orig <- solveMetaAgainstSegment parent deg gammaOrig gamma subst partialInv segment2
  let segment1 = subst <$> segment1orig
  let dom1 = _segment'content $ segment1
  let fmapPartialInv :: VarExt _ -> Maybe (VarExt _)
      fmapPartialInv VarLast = Just VarLast
      fmapPartialInv (VarWkn v) = VarWkn <$> partialInv v
  body1orig <- newRelatedTermMeta
                 parent
                 (VarWkn <$> deg)
                 (gammaOrig :.. VarFromCtx <$> segment1orig)
                 (gamma :.. VarFromCtx <$> over decl'content (\dom2 -> Pair3 dom1 dom2) segment2)
                 (fmap subst)
                 fmapPartialInv
                 (binding'body binding2)
                 tyBody1
                 tyBody2
                 "Inferring body."
  return $ Binding segment1orig body1orig

------------------------------------

solveMetaAgainstUniHSConstructor :: (MonadTC mode modty rel tc, Eq v, DeBruijnLevel v) =>
  Constraint mode modty rel ->
  rel v ->
  Ctx Type mode modty vOrig Void ->
  Ctx (Pair3 Type) mode modty v Void ->
  (vOrig -> v) ->
  (v -> Maybe vOrig) ->
  UniHSConstructor mode modty v ->
  Type mode modty v ->
  Type mode modty v ->
  tc (UniHSConstructor mode modty vOrig)
solveMetaAgainstUniHSConstructor parent deg gammaOrig gamma subst partialInv t2 ty1 ty2 =
  case t2 of
    UniHS d2 lvl2 -> do
      let nat = Type $ Expr3 $ TermCons $ ConsUniHS $ NatType
      lvl1orig <- newRelatedTermMeta parent topDeg gammaOrig gamma subst partialInv lvl2 nat nat "Inferring level."
                --newMetaTermNoCheck (Just parent) topDeg gammaOrig nat "Inferring level."
      let d1orig = unVarFromCtx <$> ctx'mode gammaOrig
      return $ UniHS d1orig lvl1orig
    Pi binding2 -> do
      let uni = Type $ Expr3 $ TermCons $ ConsUniHS $ UniHS (unVarFromCtx <$> ctx'mode gamma) (Expr3 $ TermWildcard)
      binding1orig <-
        solveMetaAgainstBinding parent deg gammaOrig gamma subst partialInv (VarWkn <$> uni) (VarWkn <$> uni) binding2
      return $ Pi $ binding1orig
    Sigma binding2 -> do
      let uni = Type $ Expr3 $ TermCons $ ConsUniHS $ UniHS (unVarFromCtx <$> ctx'mode gamma) (Expr3 $ TermWildcard)
      binding1orig <-
        solveMetaAgainstBinding parent deg gammaOrig gamma subst partialInv (VarWkn <$> uni) (VarWkn <$> uni) binding2
      return $ Sigma $ binding1orig
    EmptyType -> return EmptyType
    UnitType -> return UnitType
    BoxType boxSeg2 -> do
      boxSeg1orig <-
        solveMetaAgainstSegment parent deg gammaOrig gamma subst partialInv boxSeg2
      return $ BoxType $ boxSeg1orig
    NatType -> return NatType
    --_ -> _solveMetaAgainstUniHSConstructor

solveMetaAgainstConstructorTerm :: (MonadTC mode modty rel tc, Eq v, DeBruijnLevel v) =>
  Constraint mode modty rel ->
  rel v ->
  Ctx Type mode modty vOrig Void ->
  Ctx (Pair3 Type) mode modty v Void ->
  (vOrig -> v) ->
  (v -> Maybe vOrig) ->
  ConstructorTerm mode modty v ->
  Type mode modty v ->
  Type mode modty v ->
  tc (ConstructorTerm mode modty vOrig)
solveMetaAgainstConstructorTerm parent deg gammaOrig gamma subst partialInv t2 ty1 ty2 =
  case t2 of
    ConsUniHS c2 -> do
      c1orig <- solveMetaAgainstUniHSConstructor parent deg gammaOrig gamma subst partialInv c2 ty1 ty2
      return $ ConsUniHS $ c1orig
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
        result <- solveMetaAgainstConstructorTerm parent deg gammaOrig gamma subst partialInv c tyMeta tySolution
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
