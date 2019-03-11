module Menkar.WHN.WHN where

import Menkar.System.Fine
import Menkar.System.WHN
import Menkar.Fine.Syntax
import Menkar.Fine.Context
import Menkar.Fine.LookupQName
import Menkar.Monad.Monad

import Control.Exception.AssertFalse

import Data.Void
import Data.Maybe
import Control.Monad.Writer
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
whnormalizeElim :: (SysWHN sys, MonadTC sys tc) =>
  Constraint sys ->
  Ctx Type sys v Void ->
  ModedModality sys v {-^ how eliminee is used -} ->
  Term sys v {-^ eliminee -} ->
  UniHSConstructor sys v {-^ eliminee's type -} ->
  Eliminator sys v ->
  String ->
  WriterT [Int] tc (Term sys v)
-- careful with glue/weld!
whnormalizeElim parent gamma dmu eliminee tyEliminee e reason = do
  -- WHNormalize the eliminee
  (whnEliminee, metas) <- listen $ whnormalize parent ((VarFromCtx <$> dmu) :\\ gamma) eliminee reason
  case metas of
    -- The eliminee is blocked
    _:_ -> return $ Expr2 $ TermElim dmu whnEliminee tyEliminee e
    -- The eliminee is whnormal
    [] -> case whnEliminee of
      -- Eliminee is a variable: Elimination is neutral and hence normal.
      (Var2 v) -> return $ Expr2 $ TermElim dmu (Var2 v) tyEliminee e
      --Expr2 (TermMeta _ _) -> return $ Expr2 $ TermElim dmu whnEliminee tyEliminee e
      -- Eliminee is bogus: Return elimination as is
      (Expr2 (TermProblem _)) -> return $ Expr2 $ TermElim dmu whnEliminee tyEliminee e
      -- Eliminee is neutral: Return elimination as is
      (Expr2 (TermElim _ _ _ _)) -> return $ Expr2 $ TermElim dmu whnEliminee tyEliminee e
      -- Eliminee is system-specific: TODO
      --(Expr2 (TermSys t)) -> _
      -- Eliminee is a constructor:
      (Expr2 (TermCons t)) ->
        -- Just in case: wrap the elimination in a problem box.
        let termProblem = Expr2 $ TermProblem $ Expr2 $ TermElim dmu whnEliminee tyEliminee e
        in  case (t, e) of
          {- -Hofmann-Streicher universe code case
          (ConsUniHS d1' typeTerm, ElimUnsafeResize) -> return $ Expr2 $ TermCons $ ConsUniHS d1' $ case typeTerm of
            UniHS d1'' lvl -> UniHS d1'' lvl
            Pi (Binding seg body) ->
              Pi (Binding _seg (Expr2 $ TermElim (VarWkn <$> ModedModality d1 mu) body ElimUnsafeResize))
            _ -> _ -}
          ---------------              
          -- THE UNIVERSE
          ---------------              
          -- Elimination of a type constructor: Bogus.
          (ConsUniHS _, _) -> return termProblem
          ---------------              
          -- PI-TYPE
          ---------------
          -- Application of a lambda: Substitute and whnormalize.
          (Lam binding, App arg) ->
            let subst v = case v of
                  VarWkn w -> Var2 w
                  VarLast -> arg
            in whnormalize parent gamma (join $ subst <$> binding'body binding) reason
          -- Function extensionality over a lambda: WHNormalize the body.
          (Lam (Binding seg body), Funext) -> do
            (whnBody, metasBody) <- listen $ whnormalize parent (gamma :.. VarFromCtx <$> seg) body reason
            case (metasBody, whnBody) of
              -- Body is refl: Elimination reduces to refl.
              ([], Expr2 (TermCons (ConsRefl))) -> return $ Expr2 $ TermCons $ ConsRefl
              -- Body is blocked or neutral: Return elimination with whnormalized body.
              (_, _) -> return $ Expr2 $ TermElim dmu (Expr2 $ TermCons $ Lam $ Binding seg whnBody) tyEliminee Funext
          -- Other eliminations of lambda: Bogus.
          (Lam _, _) -> return termProblem
          ---------------              
          -- SIGMA-TYPE
          ---------------
          -- Fst of pair.
          (Pair sigmaBinding tmFst tmSnd, Fst) -> whnormalize parent gamma tmFst reason
          -- Snd of pair.
          (Pair sigmaBinding tmFst tmSnd, Snd) -> whnormalize parent gamma tmSnd reason
          -- Correct dependent elimination of pair: Substitute and whnormalize.
          (Pair sigmaBinding tmFst tmSnd, ElimDep motive (ElimSigma clause)) ->
            let subst v = case v of
                  VarWkn (VarWkn w) -> Var2 w
                  VarWkn VarLast -> tmFst
                  VarLast -> tmSnd
            in whnormalize parent gamma (join $ subst <$> _namedBinding'body (_namedBinding'body clause)) reason
          -- Other elimination of pair: Bogus.
          (Pair _ _ _, _) -> return termProblem
          ---------------              
          -- EMPTY TYPE
          ---------------
          --
          ---------------              
          -- UNIT TYPE
          ---------------
          -- Elimination of unit: Bogus.
          (ConsUnit, _) -> return termProblem
          ---------------              
          -- BOX TYPE
          ---------------
          -- Unbox box.
          (ConsBox seg tm, Unbox) -> whnormalize parent gamma tm reason
          -- Correct dependent elimination of box: Substitute and whnormalize.
          (ConsBox seg tm, ElimDep motive (ElimBox clause)) ->
            let subst :: VarExt _ -> Term _ _
                subst VarLast = tm
                subst (VarWkn v) = Var2 v
            in  whnormalize parent gamma (join $ subst <$> _namedBinding'body clause) reason
          -- Other dependent elimination of box: Bogus.
          (ConsBox _ _, _) -> return termProblem
          ---------------              
          -- NATURALS
          ---------------
          -- Correct dependent elimination of zero.
          (ConsZero, ElimDep motive (ElimNat cz cs)) -> whnormalize parent gamma cz reason
          -- Other elimination of zero: Bogus.
          (ConsZero, _) -> return termProblem
          -- Correct dependent elimination of successor: Substitute and whnormalize.
          (ConsSuc t, ElimDep motive (ElimNat cz cs)) ->
            let subst :: VarExt (VarExt _) -> Term _ _
                subst VarLast = Expr2 $ TermElim dmu t tyEliminee (ElimDep motive (ElimNat cz cs))
                subst (VarWkn VarLast) = t
                subst (VarWkn (VarWkn v)) = Var2 v
            in  whnormalize parent gamma (join $ subst <$> _namedBinding'body (_namedBinding'body cs)) reason
          -- Other elimination of zero: Bogus.
          (ConsSuc _, _) -> return termProblem
          ---------------              
          -- IDENTITY TYPE
          ---------------
          -- Correct dependent elimination of refl.
          (ConsRefl, ElimEq motive crefl) -> whnormalize parent gamma crefl reason
          -- Other elimination of refl: Bogus.
          (ConsRefl, _) -> return termProblem
      (Expr2 _) -> unreachable

whnormalizeNV :: (SysWHN sys, MonadTC sys tc) =>
  Constraint sys ->
  Ctx Type sys v Void ->
  TermNV sys v ->
  String ->
  WriterT [Int] tc (Term sys v)
-- Constructor: return it
whnormalizeNV parent gamma t@(TermCons _) reason = return $ Expr2 $ t   -- Mind glue and weld!
-- Eliminator: call whnormalizeElim
whnormalizeNV parent gamma (TermElim dmu t tyEliminee e) reason = whnormalizeElim parent gamma dmu t tyEliminee e reason
-- Meta: return if unsolved, otherwise whnormalize solution.
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
-- Wildcard: unreachable
whnormalizeNV parent gamma TermWildcard reason = unreachable
-- QName: Extract the enclosed value, turn the telescope into box-constructors and lambdas, and return.
whnormalizeNV parent gamma (TermQName qname leftDividedTelescopedVal) reason =
    let moduleMode = _leftDivided'originalMode leftDividedTelescopedVal
        telescopedVal = _leftDivided'content leftDividedTelescopedVal
        ModApplied _ quantifiedVal = telescoped2modalQuantified moduleMode telescopedVal
        quantifiedTerm = _val'term quantifiedVal
    in  whnormalize parent gamma quantifiedTerm reason
-- Results annotated with an algorithm for solving them: whnormalize the result.
whnormalizeNV parent gamma (TermAlgorithm alg result) reason = whnormalize parent gamma result reason
-- System specific terms: call whnormalizeSys, a method of SysWHN.
whnormalizeNV parent gamma (TermSys t) reason = whnormalizeSys parent gamma t reason
-- Bogus terms: return them.
whnormalizeNV parent gamma t@(TermProblem _) reason = return $ Expr2 t

{- | Either weak-head-normalizes the given term and writes nothing,
     or fails to weak-head-normalize the given term (but weak-head-normalizes as far as possible) and
     writes the indices of all metavariables that could (each in itself) unblock the situation.
-}
whnormalize :: (SysWHN sys, MonadTC sys tc) =>
  Constraint sys ->
  Ctx Type sys v Void ->
  Term sys v ->
  String ->
  WriterT [Int] tc (Term sys v)
-- Variable: return it
whnormalize parent gamma (Var2 v) reason = return $ Var2 v
-- Not a variable: call whnormalizeNV
whnormalize parent gamma (Expr2 t) reason = whnormalizeNV parent gamma t reason
