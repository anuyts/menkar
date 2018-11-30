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
import Control.Monad.Trans.Maybe

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
      t1orig <- newMetaTermNoCheck (Just parent) degOrig gammaOrig reason
      let t1 = subst <$> t1orig
      addNewConstraint
        (JudTermRel deg gamma (Pair3 t1 t2) (Pair3 ty1 ty2))
        (Just parent)
        reason
      return t1orig

newRelatedMetaType :: (MonadTC mode modty rel tc, Eq v, DeBruijnLevel v) =>
  Constraint mode modty rel ->
  rel v ->
  Ctx Type mode modty vOrig Void ->
  Ctx (Pair3 Type) mode modty v Void ->
  (vOrig -> v) ->
  (v -> Maybe vOrig) ->
  Type mode modty v ->
  String ->
  tc (Type mode modty vOrig)
newRelatedMetaType parent deg gammaOrig gamma subst partialInv ty2 reason = do
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

newRelatedSegment :: (MonadTC mode modty rel tc, Eq v, DeBruijnLevel v) =>
  Constraint mode modty rel ->
  rel v ->
  Ctx Type mode modty vOrig Void ->
  Ctx (Pair3 Type) mode modty v Void ->
  (vOrig -> v) ->
  (v -> Maybe vOrig) ->
  Segment Type mode modty v ->
  tc (Segment Type mode modty vOrig)
newRelatedSegment parent deg gammaOrig gamma subst partialInv segment2 = do
  let dmu2 = _decl'modty segment2
  -- CMODE: dmu1orig <- newRelatedModedModality dmu2 
  let dmu1orig = wildModedModality
  let dmu1 = subst <$> dmu1orig
  let ty2 = _decl'content segment2
  ty1orig <- newRelatedMetaType
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

newRelatedBinding :: (MonadTC mode modty rel tc, Eq v, DeBruijnLevel v) =>
  Constraint mode modty rel ->
  rel v ->
  Ctx Type mode modty vOrig Void ->
  Ctx (Pair3 Type) mode modty v Void ->
  (vOrig -> v) ->
  (v -> Maybe vOrig) ->
  Binding Type Term mode modty v ->
  Type mode modty (VarExt v) ->
  Type mode modty (VarExt v) ->
  tc (Binding Type Term mode modty vOrig)
newRelatedBinding parent deg gammaOrig gamma subst partialInv binding2 tyBody1 tyBody2 = do
  let segment2 = binding'segment binding2
  segment1orig <- newRelatedSegment parent deg gammaOrig gamma subst partialInv segment2
  let segment1 = subst <$> segment1orig
  let dom1 = _segment'content $ segment1
  let fmapPartialInv :: VarExt _ -> Maybe (VarExt _)
      fmapPartialInv VarLast = Just VarLast
      fmapPartialInv (VarWkn v) = VarWkn <$> partialInv v
  body1orig <- newRelatedMetaTerm
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
      lvl1orig <- newRelatedMetaTerm parent topDeg gammaOrig gamma subst partialInv lvl2 nat nat "Inferring level."
                --newMetaTermNoCheck (Just parent) topDeg gammaOrig nat "Inferring level."
      let d1orig = unVarFromCtx <$> ctx'mode gammaOrig
      return $ UniHS d1orig lvl1orig
    Pi binding2 -> do
      let uni = Type $ Expr3 $ TermCons $ ConsUniHS $ UniHS (unVarFromCtx <$> ctx'mode gamma) (Expr3 $ TermWildcard)
      binding1orig <-
        newRelatedBinding parent deg gammaOrig gamma subst partialInv binding2 (VarWkn <$> uni) (VarWkn <$> uni)
      return $ Pi $ binding1orig
    Sigma binding2 -> do
      let uni = Type $ Expr3 $ TermCons $ ConsUniHS $ UniHS (unVarFromCtx <$> ctx'mode gamma) (Expr3 $ TermWildcard)
      binding1orig <-
        newRelatedBinding parent deg gammaOrig gamma subst partialInv binding2 (VarWkn <$> uni) (VarWkn <$> uni)
      return $ Sigma $ binding1orig
    EmptyType -> return EmptyType
    UnitType -> return UnitType
    BoxType boxSeg2 -> do
      boxSeg1orig <-
        newRelatedSegment parent deg gammaOrig gamma subst partialInv boxSeg2
      return $ BoxType $ boxSeg1orig
    NatType -> return NatType

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
    Lam binding2 -> do
      case (ty1, ty2) of
        (Type (Expr3 (TermCons (ConsUniHS (Pi piBinding1)))),
         Type (Expr3 (TermCons (ConsUniHS (Pi piBinding2))))) -> do
            let cod1 = Type $ binding'body piBinding1
            let cod2 = Type $ binding'body piBinding2
            binding1orig <- newRelatedBinding parent deg gammaOrig gamma subst partialInv binding2 cod1 cod2
            return $ Lam binding1orig
        (_, _) -> tcFail parent "Terms are presumed to be well-typed."
    Pair sigmaBinding2 tmFst2 tmSnd2 -> do
      case (ty1, ty2) of
        (Type (Expr3 (TermCons (ConsUniHS (Sigma sigmaBinding1)))),
         Type (Expr3 (TermCons (ConsUniHS (Sigma sigmaBinding2))))) -> do
            let tyFst1 = _segment'content $ binding'segment sigmaBinding1
            let tyFst2 = _segment'content $ binding'segment sigmaBinding2
            let dmu1 = _segment'modty $ binding'segment sigmaBinding1
            -- CMODE: figure out modality
            let dmu1orig = wildModedModality
            tmFst1orig <- newRelatedMetaTerm parent (divDeg dmu1orig deg) (VarFromCtx <$> dmu1orig :\\ gammaOrig)
                            (VarFromCtx <$> dmu1 :\\ gamma) subst partialInv tmFst2 tyFst1 tyFst2
                            "Inferring first component."
            let tmFst1 = subst <$> tmFst1orig
            let tySnd1 = substLast3 tmFst1 $ Type $ binding'body sigmaBinding1
            let tySnd2 = substLast3 tmFst2 $ Type $ binding'body sigmaBinding2
            -- CMODE: deg should probably live in vOrig
            let degOrig = fromMaybe unreachable $ sequenceA $ partialInv <$> deg
            tyFst1orig <- newMetaTermNoCheck (Just parent) degOrig gammaOrig "Inferring type of first component."
            let sigmaSeg1orig = Declaration
                                  (_decl'name $ binding'segment $ sigmaBinding1)
                                  dmu1orig
                                  Explicit -- CMODE
                                  (Type tyFst1orig)
            tySnd1orig <- newMetaTermNoCheck (Just parent) (VarWkn <$> degOrig)
                               (gammaOrig :.. VarFromCtx <$> sigmaSeg1orig) "Inferring type of second component."
            let sigmaBinding1orig = Binding sigmaSeg1orig tySnd1orig
            tmSnd1orig <- newRelatedMetaTerm parent deg gammaOrig gamma subst partialInv tmSnd2 tySnd1 tySnd2
                            "Inferring second component."
            return $ Pair sigmaBinding1orig tmFst1orig tmSnd1orig
        (_, _) -> tcFail parent "Terms are presumed to be well-typed."
    ConsUnit -> return ConsUnit
    ConsBox boxSeg tmUnbox2 -> do
      case (ty1, ty2) of
        (Type (Expr3 (TermCons (ConsUniHS (BoxType boxSeg1)))),
         Type (Expr3 (TermCons (ConsUniHS (BoxType boxSeg2))))) -> do
            let tyUnbox1 = _segment'content boxSeg1
            let tyUnbox2 = _segment'content boxSeg2
            let dmu1 = _segment'modty boxSeg1
            -- CMODE: figure out modality
            let dmu1orig = wildModedModality
            tmUnbox1orig <- newRelatedMetaTerm parent (divDeg dmu1orig deg) (VarFromCtx <$> dmu1orig :\\ gammaOrig)
                            (VarFromCtx <$> dmu1 :\\ gamma) subst partialInv tmUnbox2 tyUnbox1 tyUnbox2
                            "Inferring box content."
            let tmUnbox1 = subst <$> tmUnbox1orig
            -- CMODE: deg should probably live in vOrig
            let degOrig = fromMaybe unreachable $ sequenceA $ partialInv <$> deg
            tyUnbox1orig <- newMetaTermNoCheck (Just parent) degOrig gammaOrig "Inferring type of box content."
            let boxSeg1orig = Declaration
                                  (_decl'name $ boxSeg1)
                                  dmu1orig
                                  Explicit -- CMODE
                                  (Type tyUnbox1orig)
            return $ ConsBox boxSeg1orig tmUnbox1orig
    ConsZero -> return ConsZero
    ConsSuc t2 -> do
      let nat = Type $ Expr3 $ TermCons $ ConsUniHS $ NatType
      t1orig <- newRelatedMetaTerm parent deg gammaOrig gamma subst partialInv t2 nat nat "Inferring predecessor."
      return $ ConsSuc t1orig

{-| Precondition: @partialInv . subst = Just@.
-}
solveMetaAgainstWHNF :: (MonadTC mode modty rel tc, Eq v, DeBruijnLevel v) =>
  Constraint mode modty rel ->
  rel v ->
  Ctx Type mode modty vOrig Void ->
  Ctx (Pair3 Type) mode modty v Void ->
  (vOrig -> v) ->
  (v -> Maybe vOrig) ->
  Term mode modty v ->
  Type mode modty v ->
  Type mode modty v ->
  tc (Term mode modty vOrig)
solveMetaAgainstWHNF parent deg gammaOrig gamma subst partialInv t2 ty1 ty2 =
  -- CMOD if deg = eqDeg and tSolution does not mention any additional variables, solve fully.
  -- Otherwise, we do a weak-head solve.
  case t2 of
    Var3 v -> case partialInv v of
      Nothing -> tcBlock
      Just u -> return $ Var3 u
    Expr3 t2 -> case t2 of
      TermCons c2 -> do
        c1orig <- solveMetaAgainstConstructorTerm parent deg gammaOrig gamma subst partialInv c2 ty1 ty2
        return $ Expr3 $ TermCons $ c1orig
      --TermElim
      TermMeta _ _ -> unreachable
      TermWildcard -> unreachable
      TermQName _ _ -> unreachable
      TermSmartElim _ _ _ -> unreachable
      TermGoal _ _ -> unreachable
      TermProblem _ -> do
        tcFail parent "Nonsensical term."
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
                Just $ solveMetaAgainstWHNF parent deg gammaOrig gamma depcySubst depcySubstInv tSolution tyMeta tySolution
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
