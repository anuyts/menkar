module Menkar.WHN.WHN where

import Menkar.System.Fine
import Menkar.Fine.Syntax
import Menkar.Fine.Context
import Menkar.Fine.LookupQName
import Menkar.Monad.Monad

import Data.Void
import Data.Maybe
import Control.Monad.Writer
import Control.Exception.AssertFalse
import Data.Functor.Compose
import Control.Monad.Trans.Maybe
import Data.Monoid

--TODOMOD means todo for modalities

{- Note about eta-rules:
   * For unit, there is no eliminator, so we need not normalize elements of Unit to unit.
   * For pairs, applying a projection to a non-constructor term yields the desired term anyway.
   * For non-projectible pairs, there was no eta-rule anyway.
   In summary, we don't eta-expand.
-}
--TODOMOD normalize tmFst in different context
--TODOMOD normalize unboxed term in different context
whnormalizeElim :: MonadTC sys tc =>
  Constraint sys ->
  Ctx Type sys v Void ->
  ModedModality sys v {-^ how eliminee is used -} ->
  Term sys v {-^ eliminee -} ->
  UniHSConstructor sys v {-^ eliminee's type -} ->
  Eliminator sys v ->
  String ->
  WriterT [Int] tc (Term sys v)
whnormalizeElim parent gamma dmu eliminee tyEliminee e reason = do
  (whnEliminee, metas) <- listen $ whnormalize parent ((VarFromCtx <$> dmu) :\\ gamma) eliminee reason
  case (metas, whnEliminee) of
    (_ : _, _) -> return $ Expr2 $ TermElim dmu whnEliminee tyEliminee e
    --Eliminations of metas are neutral and hence normal.
    ([], Var2 v) -> return $ Expr2 $ TermElim dmu (Var2 v) tyEliminee e
    --Expr2 (TermMeta _ _) -> return $ Expr2 $ TermElim dmu whnEliminee tyEliminee e
    --  -- careful with glue/weld!
    ([], Expr2 (TermProblem _)) -> return $ Expr2 $ TermElim dmu whnEliminee tyEliminee e
    ([], Expr2 (TermElim _ _ _ _)) -> return $ Expr2 $ TermElim dmu whnEliminee tyEliminee e
    ([], Expr2 (TermCons t)) ->
      let termProblem = Expr2 $ TermProblem $ Expr2 $ TermElim dmu whnEliminee tyEliminee e
      in  case (t, e) of
        {- -Hofmann-Streicher universe code case
        (ConsUniHS d1' typeTerm, ElimUnsafeResize) -> return $ Expr2 $ TermCons $ ConsUniHS d1' $ case typeTerm of
          UniHS d1'' lvl -> UniHS d1'' lvl
          Pi (Binding seg body) ->
            Pi (Binding _seg (Expr2 $ TermElim (VarWkn <$> ModedModality d1 mu) body ElimUnsafeResize))
          _ -> _ -}
        (ConsUniHS _, _) -> return termProblem
        --function case
        (Lam binding, App arg) ->
          let subst v = case v of
                VarWkn w -> Var2 w
                VarLast -> arg
          in whnormalize parent gamma (join $ subst <$> binding'body binding) reason
        (Lam (Binding seg body), Funext) -> do
          (whnBody, metasBody) <- listen $ whnormalize parent (gamma :.. VarFromCtx <$> seg) body reason
          case (metasBody, whnBody) of
            ([], Expr2 (TermCons (ConsRefl))) -> return $ Expr2 $ TermCons $ ConsRefl
            --blocked or neutral
            (_, _) -> return $ Expr2 $ TermElim dmu (Expr2 $ TermCons $ Lam $ Binding seg whnBody) tyEliminee Funext
        (Lam _, _) -> return termProblem
        --sigma cases
        (Pair sigmaBinding tmFst tmSnd, Fst) -> whnormalize parent gamma tmFst reason
        (Pair sigmaBinding tmFst tmSnd, Snd) -> whnormalize parent gamma tmSnd reason
        (Pair sigmaBinding tmFst tmSnd, ElimDep motive (ElimSigma clause)) ->
          let subst v = case v of
                VarWkn (VarWkn w) -> Var2 w
                VarWkn VarLast -> tmFst
                VarLast -> tmSnd
          in whnormalize parent gamma (join $ subst <$> _namedBinding'body (_namedBinding'body clause)) reason
        (Pair _ _ _, _) -> return termProblem
        --empty type cases (none)
        --unit cases (none)
        (ConsUnit, _) -> return termProblem
        --box cases
        (ConsBox seg tm, Unbox) -> whnormalize parent gamma tm reason
        (ConsBox seg tm, ElimDep motive (ElimBox clause)) ->
          let subst :: VarExt _ -> Term _ _
              subst VarLast = tm
              subst (VarWkn v) = Var2 v
          in  whnormalize parent gamma (join $ subst <$> _namedBinding'body clause) reason
        (ConsBox _ _, _) -> return termProblem
        --nat cases
        (ConsZero, ElimDep motive (ElimNat cz cs)) -> whnormalize parent gamma cz reason
        (ConsZero, _) -> return termProblem
        (ConsSuc t, ElimDep motive (ElimNat cz cs)) ->
          let subst :: VarExt (VarExt _) -> Term _ _
              subst VarLast = Expr2 $ TermElim dmu t tyEliminee (ElimDep motive (ElimNat cz cs))
              subst (VarWkn VarLast) = t
              subst (VarWkn (VarWkn v)) = Var2 v
          in  whnormalize parent gamma (join $ subst <$> _namedBinding'body (_namedBinding'body cs)) reason
        (ConsSuc _, _) -> return termProblem
        (ConsRefl, ElimEq motive crefl) -> whnormalize parent gamma crefl reason
        (ConsRefl, _) -> return termProblem
    ([], Expr2 _) -> unreachable

whnormalizeNV :: MonadTC sys tc =>
  Constraint sys ->
  Ctx Type sys v Void ->
  TermNV sys v ->
  String ->
  WriterT [Int] tc (Term sys v)
whnormalizeNV parent gamma t@(TermCons _) reason = return . Expr2 $ t   -- Mind glue and weld!
whnormalizeNV parent gamma (TermElim dmu t tyEliminee e) reason = whnormalizeElim parent gamma dmu t tyEliminee e reason
whnormalizeNV parent gamma t@(TermMeta etaFlag meta (Compose depcies) alg) reason = do
  --solution <- fromMaybe (Expr2 t) <$> awaitMeta parent reason meta depcies
  maybeSolution <- lift $ awaitMeta parent reason meta depcies
  case maybeSolution of
    Nothing -> Expr2 t <$ tell [meta]
    Just solution -> whnormalize parent gamma solution reason
{-maybeSolution <- getMeta meta depcies
  case maybeSolution of
    Nothing -> Expr2 t <$ tell [meta]
    Just solution -> whnormalize gamma solution-}
whnormalizeNV parent gamma TermWildcard reason = unreachable
whnormalizeNV parent gamma (TermQName qname leftDividedTelescopedVal) reason =
    let moduleMode = _leftDivided'originalMode leftDividedTelescopedVal
        telescopedVal = _leftDivided'content leftDividedTelescopedVal
        ModApplied _ quantifiedVal = telescoped2modalQuantified moduleMode telescopedVal
        quantifiedTerm = _val'term quantifiedVal
    in  whnormalize parent gamma quantifiedTerm reason
whnormalizeNV parent gamma (TermAlgorithm alg result) reason = whnormalize parent gamma result reason
whnormalizeNV parent gamma (TermSys t) reason = _
whnormalizeNV parent gamma t@(TermProblem _) reason = return $ Expr2 t

{- | Either weak-head-normalizes the given term and writes nothing,
     or fails to weak-head-normalize the given term (but weak-head-normalizes as far as possible) and
     writes the indices of all metavariables that could (each in itself) unblock the situation.
-}
whnormalize :: MonadTC sys tc =>
  Constraint sys ->
  Ctx Type sys v Void ->
  Term sys v ->
  String ->
  WriterT [Int] tc (Term sys v)
whnormalize parent gamma (Var2 v) reason = return $ Var2 v
whnormalize parent gamma (Expr2 t) reason = whnormalizeNV parent gamma t reason
