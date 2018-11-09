module Menkar.Fine.WHNormalize where

import Menkar.Fine.Syntax
import Menkar.Fine.Context
import Menkar.Fine.LookupQName
import Menkar.Fine.Multimode
import Data.Void
import Control.Monad.Writer
import Control.Exception.AssertFalse

--TODOMOD means todo for modalities

{- Note about eta-rules:
   * For unit, there is no eliminator, so we need not normalize elements of Unit to unit.
   * For pairs, applying a projection to a non-constructor term yields the desired term anyway.
   * For non-projectible pairs, there was no eta-rule anyway.
   In summary, we don't eta-expand.
-}
--TODOMOD normalize tmFst in different context
--TODOMOD normalize unboxed term in different context
whnormalizeElim :: Multimode mode modty =>
  Ctx Type mode modty v Void ->
  ModedModality mode modty v {-^ how eliminee is used -} ->
  Term mode modty v {-^ eliminee -} ->
  Type mode modty v {-^ eliminee's type -} ->
  Eliminator mode modty v ->
  Writer [Int] (Term mode modty v)
whnormalizeElim gamma dmu eliminee tyEliminee e = do
  whnEliminee <- whnormalize ((VarFromCtx <$> dmu) :\\ gamma) eliminee
  case whnEliminee of
    Var3 v -> return $ Expr3 $ TermElim dmu (Var3 v) tyEliminee e
    Expr3 (TermMeta _ _) -> return $ Expr3 $ TermElim dmu whnEliminee tyEliminee e
      -- careful with glue/weld!
    Expr3 (TermProblem _) -> return $ Expr3 $ TermElim dmu whnEliminee tyEliminee e
    Expr3 (TermCons t) -> case (t, e) of
      {- -Hofmann-Streicher universe code case
      (ConsUniHS d1' typeTerm, ElimUnsafeResize) -> return $ Expr3 $ TermCons $ ConsUniHS d1' $ case typeTerm of
        UniHS d1'' lvl -> UniHS d1'' lvl
        Pi (Binding seg body) ->
          Pi (Binding _seg (Expr3 $ TermElim (VarWkn <$> ModedModality d1 mu) body ElimUnsafeResize))
        _ -> _ -}
      --function case
      (Lam binding, App arg) ->
        let subst v = case v of
              VarWkn w -> Var3 w
              VarLast -> arg
              _ -> unreachable
        in whnormalize gamma (join $ subst <$> binding'body binding)
      --sigma cases
      (Pair sigmaBinding tmFst tmSnd, Fst) -> whnormalize gamma tmFst
      (Pair sigmaBinding tmFst tmSnd, Snd) -> whnormalize gamma tmSnd
      (Pair sigmaBinding tmFst tmSnd, ElimSigma motive clause) ->
        let subst v = case v of
              VarWkn (VarWkn w) -> Var3 w
              VarWkn VarLast -> tmFst
              VarLast -> tmSnd
              _ -> unreachable
        in whnormalize gamma (join $ subst <$> _namedBinding'body (_namedBinding'body clause))
      --empty type cases (none)
      --unit cases (none)
      --box cases
      (ConsBox seg tm, Unbox) -> whnormalize gamma tm
      --nat cases
      (ConsZero, ElimNat motive cz cs) -> whnormalize gamma cz
      (ConsSuc t, ElimNat motive cz cs) -> whnormalize gamma $
        let subst :: VarExt (VarExt _) -> Term _ _ _
            subst VarLast = Expr3 $ TermElim dmu t tyEliminee (ElimNat motive cz cs)
            subst (VarWkn VarLast) = t
            subst (VarWkn (VarWkn v)) = Var3 v
            subst (VarWkn v) = unreachable
            subst v = unreachable
        in  join $ subst <$> _namedBinding'body (_namedBinding'body cs)
      --nonsensical cases
      (_, _) -> return $ Expr3 $ TermProblem $ Expr3 $ TermElim dmu whnEliminee tyEliminee e
    Expr3 _ -> unreachable

whnormalizeNV :: Multimode mode modty =>
  Ctx Type mode modty v Void ->
  TermNV mode modty v ->
  Writer [Int] (Term mode modty v)
whnormalizeNV gamma t@(TermCons _) = return . Expr3 $ t   -- Mind glue and weld!
whnormalizeNV gamma (TermElim dmu t tyEliminee e) = whnormalizeElim gamma dmu t tyEliminee e
whnormalizeNV gamma t@(TermMeta i depcies) = Expr3 t <$ tell [i]
whnormalizeNV gamma (TermQName qname) = case lookupQName gamma qname of
  Nothing -> return $ Expr3 $ TermProblem $ Expr3 $ TermQName qname
  Just leftDividedTelescopedVal ->
    let telescopedVal = _leftDivided'content leftDividedTelescopedVal
        ModApplied _ quantifiedVal = telescoped2modalQuantified telescopedVal
        quantifiedTerm = _val'term quantifiedVal
    in  whnormalize gamma (unVarFromCtx <$> quantifiedTerm)
whnormalizeNV gamma (TermSmartElim eliminee eliminators result) = whnormalize gamma result
whnormalizeNV gamma (TermGoal str result) = whnormalize gamma result
whnormalizeNV gamma t@(TermProblem _) = return $ Expr3 t

whnormalize :: Multimode mode modty =>
  Ctx Type mode modty v Void ->
  Term mode modty v ->
  Writer [Int] (Term mode modty v)
whnormalize gamma (Var3 v) = return $ Var3 v
whnormalize gamma (Expr3 t) = whnormalizeNV gamma t
