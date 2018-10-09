module Menkar.Fine.WHNormalize where

import Menkar.Fine.Syntax
import Menkar.Fine.Substitution
import Menkar.Fine.Context.Variable
import Menkar.Fine.Context
import Menkar.Fine.LookupQName
import Data.Void
import Control.Monad.Writer
import Control.Exception.AssertFalse

{- Note about eta-rules:
   * For unit, there is no eliminator, so we need not normalize elements of Unit to unit.
   * For pairs, applying a projection to a non-constructor term yields the desired term anyway.
   * For non-projectible pairs, there was no eta-rule anyway.
   In summary, we don't eta-expand.
-}
whnormalizeElim :: (Functor mode, Functor modty, CanSwallow (Term mode modty) mode, CanSwallow (Term mode modty) modty) =>
  Ctx Type mode modty v Void ->
  mode v {-^ eliminee's mode -} ->
  mode v {-^ result mode -} ->
  modty v ->
  Term mode modty v {-^ eliminee -} ->
  Eliminator mode modty v ->
  Writer [Int] (Term mode modty v)
whnormalizeElim gamma d1 d2 mu eliminee e = do
  whnEliminee <- whnormalize ((VarFromCtx <$> ModedContramodality d2 mu) :\\ gamma) (VarDiv <$> d1) (VarDiv <$> eliminee)
  case whnEliminee of
    Var3 (VarDiv v) -> return $ Expr3 $ TermElim (ModedModality d1 mu) (Var3 v) e
    Expr3 (TermMeta _ _) -> return $ Expr3 $ TermElim (ModedModality d1 mu) (runVarDiv <$> whnEliminee) e
    Expr3 (TermProblem _) -> return $ Expr3 $ TermElim (ModedModality d1 mu) (runVarDiv <$> whnEliminee) e
    Expr3 (TermCons t) -> case (t, e) of
      --function case
      (Lam binding, App piBinding arg) ->
        let subst v = case v of
              VarLast -> arg
              VarWkn (VarDiv w) -> Var3 w
              _ -> unreachable
        in whnormalize gamma d2 (join $ subst <$> binding'body binding)
      --sigma cases
      (Pair sigmaBinding tmFst tmSnd, Fst sigmaBinding') -> whnormalize gamma d2 (runVarDiv <$> tmFst)
      (Pair sigmaBinding tmFst tmSnd, Snd sigmaBinding') -> whnormalize gamma d2 (runVarDiv <$> tmSnd)
      (Pair sigmaBinding tmFst tmSnd, ElimPair motive clause) ->
        let subst v = case v of
              VarLast -> runVarDiv <$> tmSnd
              VarWkn VarLast -> runVarDiv <$> tmFst
              VarWkn (VarWkn w) -> Var3 w
              _ -> unreachable
        in whnormalize gamma d2 (join $ subst <$> binding'body (binding'body clause))
      --empty type cases (none)
      --unit cases (none)
      --nonsensical cases
      (_, _) -> return $ Expr3 $ TermProblem $ Expr3 $ TermElim (ModedModality d1 mu) (runVarDiv <$> whnEliminee) e
    Expr3 _ -> unreachable

whnormalizeNV :: (Functor mode, Functor modty, CanSwallow (Term mode modty) mode, CanSwallow (Term mode modty) modty) =>
  Ctx Type mode modty v Void ->
  mode v ->
  TermNV mode modty v ->
  Writer [Int] (Term mode modty v)
whnormalizeNV gamma d t@(TermCons _) = return . Expr3 $ t   -- Mind glue and weld!
whnormalizeNV gamma d (TermElim dmu t e) = whnormalizeElim gamma (modality'dom dmu) d (modality'mod dmu) t e
whnormalizeNV gamma d t@(TermMeta i depcies) = Expr3 t <$ tell [i]
whnormalizeNV gamma d (TermQName qname) = case lookupQName gamma qname of
  Nothing -> return $ Expr3 $ TermProblem $ Expr3 $ TermQName qname
  Just t -> whnormalize gamma d (unVarFromCtx <$> t)
whnormalizeNV gamma d (TermSmartElim eliminee eliminators result) = whnormalize gamma d result
whnormalizeNV gamma d (TermGoal str result) = whnormalize gamma d result
whnormalizeNV gamma d t@(TermProblem _) = return $ Expr3 t

whnormalize :: (Functor mode, Functor modty, CanSwallow (Term mode modty) mode, CanSwallow (Term mode modty) modty) =>
  Ctx Type mode modty v Void ->
  mode v -> 
  Term mode modty v ->
  Writer [Int] (Term mode modty v)
whnormalize gamma d (Var3 v) = return $ Var3 v
whnormalize gamma d (Expr3 t) = whnormalizeNV gamma d t
