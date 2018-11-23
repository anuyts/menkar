module Menkar.TC.Inference.Rel where

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

checkTermRelNoEta :: (MonadTC mode modty rel tc, Eq v) =>
  Constraint mode modty rel ->
  rel v ->
  Ctx (Pair3 Type) mode modty v Void ->
  Term mode modty v ->
  Term mode modty v ->
  [Int] ->
  [Int] ->
  Type mode modty v ->
  Type mode modty v ->
  tc ()
checkTermRelNoEta parent deg gamma t1 t2 metasT1 metasT2 (Type ty1) (Type ty2) = _checkTermRelNoEta

checkTermRelKnownTypes :: (MonadTC mode modty rel tc, Eq v) =>
  Constraint mode modty rel ->
  rel v ->
  Ctx (Pair3 Type) mode modty v Void ->
  Term mode modty v ->
  Term mode modty v ->
  [Int] ->
  [Int] ->
  Type mode modty v ->
  Type mode modty v ->
  tc ()
checkTermRelKnownTypes parent deg gamma t1 t2 metasT1 metasT2 (Type ty1) (Type ty2) = case (ty1, ty2) of
  (Expr3 (TermCons (ConsUniHS (Pi piBinding1))), Expr3 (TermCons (ConsUniHS (Pi piBinding2)))) -> do
    let seg1 = binding'segment piBinding1
    let dom2 = _segment'content $ binding'segment piBinding2
    let seg = over decl'content (\ dom1 -> Pair3 dom1 dom2) seg1
    let app1 = Expr3 $ TermElim
          (idModedModality $ VarWkn . unVarFromCtx <$> ctx'mode gamma)
          (VarWkn <$> t1) (Type $ VarWkn <$> ty1) (App $ Var3 VarLast)
    let app2 = Expr3 $ TermElim
          (idModedModality $ VarWkn . unVarFromCtx <$> ctx'mode gamma)
          (VarWkn <$> t2) (Type $ VarWkn <$> ty2) (App $ Var3 VarLast)
    addNewConstraint
      (JudTermRel
        (VarWkn <$> deg)
        (gamma :.. VarFromCtx <$> seg)
        (Pair3 app1 app2)
        (Pair3
          (Type $ binding'body piBinding1)
          (Type $ binding'body piBinding2)
        )
      )
      (Just parent)
      "Eta: Relating function bodies."
  (Expr3 (TermCons (ConsUniHS (Pi piBinding1))), _) ->
    tcFail parent "Types are presumed to be related."
  (Expr3 (TermCons (ConsUniHS (Sigma sigmaBinding1))), Expr3 (TermCons (ConsUniHS (Sigma sigmaBinding2)))) -> do
    let dmu = _segment'modty $ binding'segment $ sigmaBinding1
    let d' = unVarFromCtx <$> ctx'mode gamma
    let fst1 = Expr3 $ TermElim (modedApproxLeftAdjointProj dmu d') t1 (Type ty1) Fst
    let fst2 = Expr3 $ TermElim (modedApproxLeftAdjointProj dmu d') t2 (Type ty2) Fst
    let snd1 = Expr3 $ TermElim (idModedModality d') t1 (Type t1) Snd
    let snd2 = Expr3 $ TermElim (idModedModality d') t2 (Type t2) Snd
    if not (sigmaHasEta dmu d')
      then checkTermRelNoEta  parent deg gamma t1 t2 metasT1 metasT2 (Type ty1) (Type ty2)
      else do
        addNewConstraint
          (JudTermRel
            (divDeg dmu deg)
            (VarFromCtx <$> dmu :\\ gamma)
            (Pair3 fst1 fst2)
            (Pair3
              (_segment'content $ binding'segment sigmaBinding1)
              (_segment'content $ binding'segment sigmaBinding2)
            )
          )
          (Just parent)
          "Eta: Relating first projections."
        addNewConstraint
          (JudTermRel
            deg
            gamma
            (Pair3 snd1 snd2)
            (Pair3
              (Type $ substLast3 fst1 $ binding'body sigmaBinding1)
              (Type $ substLast3 fst2 $ binding'body sigmaBinding2)
            )
          )
          (Just parent)
          "Eta: relating second projections"
  (Expr3 (TermCons (ConsUniHS (Sigma sigmaBinding1))), _) ->
    tcFail parent "Types are presumed to be related."
  (Expr3 (TermCons (ConsUniHS UnitType)), Expr3 (TermCons (ConsUniHS UnitType))) -> return ()
  (Expr3 (TermCons (ConsUniHS UnitType)), _) ->
    tcFail parent "Types are presumed to be related."
  (Expr3 (TermCons (ConsUniHS (BoxType boxSeg1))), Expr3 (TermCons (ConsUniHS (BoxType boxSeg2)))) -> do
    let dmu = _segment'modty $ boxSeg1
    let d' = unVarFromCtx <$> ctx'mode gamma
    let unbox1 = Expr3 $ TermElim (modedApproxLeftAdjointProj dmu d') t1 (Type ty1) Unbox
    let unbox2 = Expr3 $ TermElim (modedApproxLeftAdjointProj dmu d') t2 (Type ty2) Unbox
    if not (sigmaHasEta dmu d')
      then checkTermRelNoEta  parent deg gamma t1 t2 metasT1 metasT2 (Type ty1) (Type ty2)
      else do
        addNewConstraint
          (JudTermRel
            (divDeg dmu deg)
            (VarFromCtx <$> dmu :\\ gamma)
            (Pair3 unbox1 unbox2)
            (Pair3
              (_segment'content boxSeg1)
              (_segment'content boxSeg2)
            )
          )
          (Just parent)
          "Eta: Relating box contents."
  (Expr3 (TermCons (ConsUniHS (BoxType boxSeg1))), _) ->
    tcFail parent "Types are presumed to be related."
  (_, _) -> checkTermRelNoEta parent deg gamma t1 t2 metasT1 metasT2 (Type ty1) (Type ty2)

checkTermRel :: (MonadTC mode modty rel tc, Eq v) =>
  Constraint mode modty rel ->
  rel v ->
  Ctx (Pair3 Type) mode modty v Void ->
  Term mode modty v ->
  Term mode modty v ->
  Type mode modty v ->
  Type mode modty v ->
  tc ()
checkTermRel parent deg gamma t1 t2 (Type ty1) (Type ty2) =
  -- Top-relatedness is always ok.
  if isTopDeg deg
    then return ()
    else do
      -- Weak-head-normalize everything
      (whnT1, metasT1) <- runWriterT $ whnormalize (fstCtx gamma) t1
      (whnT2, metasT2) <- runWriterT $ whnormalize (sndCtx gamma) t2
      (whnTy1, metasTy1) <- runWriterT $ whnormalize (fstCtx gamma) t1
      (whnTy2, metasTy2) <- runWriterT $ whnormalize (sndCtx gamma) t2
      whnparent <- Constraint
            (JudTermRel
              deg
              gamma
              (Pair3 whnT1 whnT2)
              (Pair3 (Type whnTy1) (Type whnTy2))
            )
            (Just parent)
            "Weak-head-normalize everything"
            <$> newConstraintID
      case (whnT1, whnT2) of
        -- If both sides are constructors: compare them
        (Expr3 (TermCons c1), Expr3 (TermCons c2)) -> _checkConstructorTermRel
        -- Otherwise, we want to eta-expand, so one of the types needs to be weak-head-normal
        (_, _) -> case (metasTy1, metasTy2) of
          -- Both types are whnormal
          ([], []) -> checkTermRelKnownTypes whnparent deg gamma whnT1 whnT2 metasT1 metasT2 (Type whnTy1) (Type whnTy2)
          -- Either type is not normal
          (_, _) -> blockOnMetas (metasT1 ++ metasT2 ++ metasTy1 ++ metasTy2) whnparent
          {-
          -- whnTy1 is whnormal
          ([], _) -> checkTermRelKnownType whnparent deg gamma whnT1 whnT2 metasT1 metasT2
                       (Type whnTy1) (Type whnTy2) (Type whnTy1)
          -- whnTy1 is blocked, but whnTy2 is normal
          (_, []) -> checkTermRelKnownType whnparent deg gamma whnT1 whnT2 metasT1 metasT2
                      (Type whnTy1) (Type whnTy2) (Type whnTy2)
          -- Both types are blocked. We may need to eta-expand but cannot. Hence, we cannot proceed.
          (_, _) -> blockOnMetas (metasT1 ++ metasT2 ++ metasTy1 ++ metasTy2) whnparent
          -}
          
      {- CANNOT COMPARE VARIABLES YET: what if we're in the unit type?
      case (whnT1, whnT2) of
        (Var3 v1, Var3 v2) -> if v1 == v2
          then return ()
          else tcFail parent "Cannot relate different variables."
        (Expr3 tnv1, Expr3 tnv2) -> _compareExprs
        (Var3 _, Expr3 _) -> tcFail parent "Cannot relate variable and non-variable."
        (Expr3 _, Var3 _) -> tcFail parent "Cannot relate non-variable and variable."
      -}

checkTypeRel :: (MonadTC mode modty rel tc, Eq v) =>
  Constraint mode modty rel ->
  rel v ->
  Ctx (Pair3 Type) mode modty v Void ->
  Type mode modty v ->
  Type mode modty v ->
  tc ()
checkTypeRel parent deg gamma (Type ty1) (Type ty2) =
  let uni = Type $ Expr3 $ TermCons $ ConsUniHS $ UniHS (unVarFromCtx <$> ctx'mode gamma) (Expr3 $ TermWildcard)
  in  addNewConstraint
        (JudTermRel
          deg
          gamma
          (Pair3 ty1 ty2)
          (Pair3 uni uni)
        )
        (Just parent)
        "Checking equality of types in a Hofmann-Streicher universe."
