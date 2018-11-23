module Menkar.Fine.WHNormalize where

import Menkar.Fine.Syntax
import Menkar.Fine.Context
import Menkar.Fine.LookupQName
import Menkar.Fine.Multimode
import Menkar.TC.Monad

import Data.Void
import Control.Monad.Writer
import Control.Exception.AssertFalse
import Data.Functor.Compose

--TODOMOD means todo for modalities

{- Note about eta-rules:
   * For unit, there is no eliminator, so we need not normalize elements of Unit to unit.
   * For pairs, applying a projection to a non-constructor term yields the desired term anyway.
   * For non-projectible pairs, there was no eta-rule anyway.
   In summary, we don't eta-expand.
-}
--TODOMOD normalize tmFst in different context
--TODOMOD normalize unboxed term in different context
whnormalizeElim :: MonadTC mode modty rel tc =>
  Ctx Type mode modty v Void ->
  ModedModality mode modty v {-^ how eliminee is used -} ->
  Term mode modty v {-^ eliminee -} ->
  Type mode modty v {-^ eliminee's type -} ->
  Eliminator mode modty v ->
  WriterT [Int] tc (Term mode modty v)
whnormalizeElim gamma dmu eliminee tyEliminee e = do
  whnEliminee <- whnormalize ((VarFromCtx <$> dmu) :\\ gamma) eliminee
  case whnEliminee of
    Var3 v -> return $ Expr3 $ TermElim dmu (Var3 v) tyEliminee e
    Expr3 (TermMeta _ _) -> return $ Expr3 $ TermElim dmu whnEliminee tyEliminee e
      -- careful with glue/weld!
    Expr3 (TermProblem _) -> return $ Expr3 $ TermElim dmu whnEliminee tyEliminee e
    Expr3 (TermCons t) ->
      let termProblem = Expr3 $ TermProblem $ Expr3 $ TermElim dmu whnEliminee tyEliminee e
      in  case (t, e) of
        {- -Hofmann-Streicher universe code case
        (ConsUniHS d1' typeTerm, ElimUnsafeResize) -> return $ Expr3 $ TermCons $ ConsUniHS d1' $ case typeTerm of
          UniHS d1'' lvl -> UniHS d1'' lvl
          Pi (Binding seg body) ->
            Pi (Binding _seg (Expr3 $ TermElim (VarWkn <$> ModedModality d1 mu) body ElimUnsafeResize))
          _ -> _ -}
        (ConsUniHS _, _) -> return termProblem
        --function case
        (Lam binding, App arg) ->
          let subst v = case v of
                VarWkn w -> Var3 w
                VarLast -> arg
                _ -> unreachable
          in whnormalize gamma (join $ subst <$> binding'body binding)
        (Lam _, _) -> return termProblem
        --sigma cases
        (Pair sigmaBinding tmFst tmSnd, Fst) -> whnormalize gamma tmFst
        (Pair sigmaBinding tmFst tmSnd, Snd) -> whnormalize gamma tmSnd
        (Pair sigmaBinding tmFst tmSnd, ElimDep motive (ElimSigma clause)) ->
          let subst v = case v of
                VarWkn (VarWkn w) -> Var3 w
                VarWkn VarLast -> tmFst
                VarLast -> tmSnd
                _ -> unreachable
          in whnormalize gamma (join $ subst <$> _namedBinding'body (_namedBinding'body clause))
        (Pair _ _ _, _) -> return termProblem
        --empty type cases (none)
        --unit cases (none)
        (ConsUnit, _) -> return termProblem
        --box cases
        (ConsBox seg tm, Unbox) -> whnormalize gamma tm
        (ConsBox seg tm, ElimDep motive (ElimBox clause)) ->
          let subst :: VarExt _ -> Term _ _ _
              subst VarLast = tm
              subst (VarWkn v) = Var3 v
              subst _ = unreachable
          in  whnormalize gamma (join $ subst <$> _namedBinding'body clause)
        (ConsBox _ _, _) -> return termProblem
        --nat cases
        (ConsZero, ElimDep motive (ElimNat cz cs)) -> whnormalize gamma cz
        (ConsZero, _) -> return termProblem
        (ConsSuc t, ElimDep motive (ElimNat cz cs)) ->
          let subst :: VarExt (VarExt _) -> Term _ _ _
              subst VarLast = Expr3 $ TermElim dmu t tyEliminee (ElimDep motive (ElimNat cz cs))
              subst (VarWkn VarLast) = t
              subst (VarWkn (VarWkn v)) = Var3 v
              subst (VarWkn v) = unreachable
              subst v = unreachable
          in  whnormalize gamma (join $ subst <$> _namedBinding'body (_namedBinding'body cs))
        (ConsSuc _, _) -> return termProblem
    Expr3 _ -> unreachable

whnormalizeNV :: MonadTC mode modty rel tc =>
  Ctx Type mode modty v Void ->
  TermNV mode modty v ->
  WriterT [Int] tc (Term mode modty v)
whnormalizeNV gamma t@(TermCons _) = return . Expr3 $ t   -- Mind glue and weld!
whnormalizeNV gamma (TermElim dmu t tyEliminee e) = whnormalizeElim gamma dmu t tyEliminee e
whnormalizeNV gamma t@(TermMeta meta (Compose depcies)) = do
  maybeSolution <- getMeta meta depcies
  case maybeSolution of
    Nothing -> Expr3 t <$ tell [meta]
    Just solution -> whnormalize gamma solution
whnormalizeNV gamma (TermQName qname leftDividedTelescopedVal) =
    let telescopedVal = _leftDivided'content leftDividedTelescopedVal
        ModApplied _ quantifiedVal = telescoped2modalQuantified telescopedVal
        quantifiedTerm = _val'term quantifiedVal
    in  whnormalize gamma quantifiedTerm
whnormalizeNV gamma (TermSmartElim eliminee eliminators result) = whnormalize gamma result
whnormalizeNV gamma (TermGoal str result) = whnormalize gamma result
whnormalizeNV gamma t@(TermProblem _) = return $ Expr3 t

{- | Either weak-head-normalizes the given term and writes nothing,
     or fails to weak-head-normalize the given term (but weak-head-normalizes as far as possible) and
     writes the indices of all metavariables that could (each in itself) unblock the situation.
-}
whnormalize :: MonadTC mode modty rel tc =>
  Ctx Type mode modty v Void ->
  Term mode modty v ->
  WriterT [Int] tc (Term mode modty v)
whnormalize gamma (Var3 v) = return $ Var3 v
whnormalize gamma (Expr3 t) = whnormalizeNV gamma t
