module Menkar.WHN.WHN where

import Menkar.System.Fine
import Menkar.System.WHN
import Menkar.Fine.Syntax
import Menkar.Fine.Context
import Menkar.Fine.LookupQName
import Menkar.Monad.Monad
import Menkar.Analyzer

import Control.Exception.AssertFalse

import Data.Void
import Data.Maybe
import Control.Monad.Writer
import Data.Functor.Compose
import Data.Monoid
import Control.Monad.Writer.Class
import GHC.Generics

tryDependentEta :: (SysWHN sys, MonadWHN sys whn, DeBruijnLevel v, MonadWriter [Int] whn) =>
  Constraint sys ->
  Ctx Type sys v Void ->
  ModedModality sys v {-^ how eliminee is used -} ->
  Term sys v {-^ eliminee, whnormal -} ->
  UniHSConstructor sys v {-^ eliminee's type -} ->
  Eliminator sys v ->
  Type sys v {-^ type of the result -} ->
  String ->
  whn (Term sys v)
tryDependentEta parent gamma dmu whnEliminee tyEliminee e tyResult reason = do
  let dgamma' = ctx'mode gamma
  let dgamma = unVarFromCtx <$> dgamma'
  let returnElim = return $ Expr2 $ TermElim dmu whnEliminee tyEliminee e
  case e of
    ElimDep motive clauses -> case clauses of
      ElimSigma pairClause -> case tyEliminee of
        Sigma sigmaBinding -> do
          let dmuSigma = _segment'modty $ binding'segment sigmaBinding
          allowsEta parent (crispModedModality dgamma' :\\ gamma) dmuSigma reason >>= \case
            Just True -> do
              let tmFst = Expr2 $ TermElim (modedApproxLeftAdjointProj dmuSigma) whnEliminee tyEliminee Fst
              let tmSnd = Expr2 $ TermElim (idModedModality dgamma)              whnEliminee tyEliminee Snd
              let subst v = case v of
                    VarWkn (VarWkn w) -> Var2 w
                    VarWkn VarLast -> tmFst
                    VarLast -> tmSnd
              whnormalize parent gamma (join $ subst <$> _namedBinding'body (_namedBinding'body pairClause)) tyResult reason
            _ -> returnElim
        _ -> unreachable
      ElimBox boxClause -> case tyEliminee of
        BoxType boxSeg -> do
          let dmuBox = _segment'modty boxSeg
          allowsEta parent (crispModedModality dgamma' :\\ gamma) dmuBox reason >>= \case
            Just True -> do
              let tmUnbox = Expr2 $ TermElim (modedApproxLeftAdjointProj dmuBox) whnEliminee tyEliminee Unbox
              let subst v = case v of
                    VarWkn w -> Var2 w
                    VarLast -> tmUnbox
              whnormalize parent gamma (join $ subst <$> _namedBinding'body boxClause) tyResult reason
            _ -> returnElim
        _ -> unreachable
      ElimEmpty -> returnElim
      ElimNat _ _ -> returnElim
    _ -> returnElim

{- Note about eta-rules:
   * For unit, there is no eliminator, so we need not normalize elements of Unit to unit.
   * For pairs, applying a projection to a non-constructor term yields the desired term anyway.
   * For non-projectible pairs, there was no eta-rule anyway.
   In summary, we don't eta-expand.
-}
whnormalizeElim :: (SysWHN sys, MonadWHN sys whn, DeBruijnLevel v, MonadWriter [Int] whn) =>
  Constraint sys ->
  Ctx Type sys v Void ->
  ModedModality sys v {-^ how eliminee is used -} ->
  Term sys v {-^ eliminee -} ->
  UniHSConstructor sys v {-^ eliminee's type -} ->
  Eliminator sys v ->
  Type sys v {-^ type of the result -} ->
  [Int] ->
  String ->
  whn (Term sys v)
-- careful with glue/weld!
whnormalizeElim parent gamma dmu whnEliminee tyEliminee e tyResult metasEliminee reason = do
  let dgamma = unVarFromCtx <$> ctx'mode gamma
  -- WHNormalize the eliminee
  --(whnEliminee, metas) <- listen $ whnormalize parent ((VarFromCtx <$> dmu) :\\ gamma) eliminee (hs2type tyEliminee) reason
  let useDependentEta = tryDependentEta parent gamma dmu whnEliminee tyEliminee e tyResult reason
  case metasEliminee of
    -- The eliminee is blocked: Try to rely on eta instead
    _:_ -> useDependentEta
      --return $ Expr2 $ TermElim dmu whnEliminee tyEliminee e
    -- The eliminee is whnormal
    [] -> case whnEliminee of
      -- Eliminee is a variable: Try to rely on eta instead.
      (Var2 v) -> useDependentEta
      -- Eliminee is bogus: Try to rely on eta instead
      (Expr2 (TermProblem _)) -> useDependentEta
      -- Eliminee is neutral: Try to rely on eta instead
      (Expr2 (TermElim _ _ _ _)) -> useDependentEta
      (Expr2 (TermMeta MetaNeutral meta depcies alg)) -> useDependentEta
      -- Eliminee is system-specific: considered neutral, as there are no system-specific eliminators right now.
      (Expr2 (TermSys t)) -> useDependentEta
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
            in whnormalize parent gamma (join $ subst <$> binding'body binding) tyResult reason
          -- Function extensionality over a lambda: WHNormalize the body. (The analyzer doesn't do that!)
          (Lam (Binding seg body), Funext) -> do
            let Pi piBinding = tyEliminee
            whnBody <- whnormalize parent (gamma :.. VarFromCtx <$> seg) body (binding'body piBinding) reason
            case whnBody of
              -- Body is refl: Elimination reduces to refl.
              Expr2 (TermCons (ConsRefl tyAmbient t)) ->
                return $ Expr2 $ TermCons $ ConsRefl
                  (hs2type $ Pi $ Binding seg tyAmbient)
                  (Expr2 $ TermCons $ Lam $ Binding seg t)
              -- Body is blocked or neutral: Return elimination with whnormalized body.
              _ -> return $ Expr2 $ TermElim dmu (Expr2 $ TermCons $ Lam $ Binding seg whnBody) tyEliminee Funext
          -- Other eliminations of lambda: Bogus.
          (Lam _, _) -> return termProblem
          ---------------              
          -- SIGMA-TYPE
          ---------------
          -- Fst of pair.
          (Pair sigmaBinding tmFst tmSnd, Fst) -> whnormalize parent gamma tmFst tyResult reason
          -- Snd of pair.
          (Pair sigmaBinding tmFst tmSnd, Snd) -> whnormalize parent gamma tmSnd tyResult reason
          -- Correct dependent elimination of pair: Substitute and whnormalize.
          (Pair sigmaBinding tmFst tmSnd, ElimDep motive (ElimSigma clause)) ->
            let subst v = case v of
                  VarWkn (VarWkn w) -> Var2 w
                  VarWkn VarLast -> tmFst
                  VarLast -> tmSnd
            in whnormalize parent gamma (join $ subst <$> _namedBinding'body (_namedBinding'body clause)) tyResult reason
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
          (ConsBox seg tm, Unbox) -> whnormalize parent gamma tm tyResult reason
          -- Correct dependent elimination of box: Substitute and whnormalize.
          (ConsBox seg tm, ElimDep motive (ElimBox clause)) ->
            let subst :: VarExt _ -> Term _ _
                subst VarLast = tm
                subst (VarWkn v) = Var2 v
            in  whnormalize parent gamma (join $ subst <$> _namedBinding'body clause) tyResult reason
          -- Other dependent elimination of box: Bogus.
          (ConsBox _ _, _) -> return termProblem
          ---------------              
          -- NATURALS
          ---------------
          -- Correct dependent elimination of zero.
          (ConsZero, ElimDep motive (ElimNat cz cs)) -> whnormalize parent gamma cz tyResult reason
          -- Other elimination of zero: Bogus.
          (ConsZero, _) -> return termProblem
          -- Correct dependent elimination of successor: Substitute and whnormalize.
          (ConsSuc t, ElimDep motive (ElimNat cz cs)) ->
            let subst :: VarExt (VarExt _) -> Term _ _
                subst VarLast = Expr2 $ TermElim dmu t tyEliminee (ElimDep motive (ElimNat cz cs))
                subst (VarWkn VarLast) = t
                subst (VarWkn (VarWkn v)) = Var2 v
            in  whnormalize parent gamma (join $ subst <$> _namedBinding'body (_namedBinding'body cs)) tyResult reason
          -- Other elimination of zero: Bogus.
          (ConsSuc _, _) -> return termProblem
          ---------------              
          -- IDENTITY TYPE
          ---------------
          -- Correct dependent elimination of refl.
          (ConsRefl tyAmbient t, ElimEq motive crefl) -> whnormalize parent gamma crefl tyResult reason
          -- Other elimination of refl: Bogus.
          (ConsRefl _ _, _) -> return termProblem
      (Expr2 _) -> unreachable

whnormalizeNV :: (SysWHN sys, MonadWHN sys whn, DeBruijnLevel v, MonadWriter [Int] whn) =>
  Constraint sys ->
  Ctx Type sys v Void ->
  TermNV sys v ->
  Type sys v ->
  [Int] ->
  String ->
  whn (Term sys v)
-- Constructor: return it
whnormalizeNV parent gamma t@(TermCons _) ty metas reason = return $ Expr2 $ t   -- Mind glue and weld!
-- Eliminator: call whnormalizeElim
whnormalizeNV parent gamma (TermElim dmu t tyEliminee e) ty metas reason =
  whnormalizeElim parent gamma dmu t tyEliminee e ty metas reason
-- Meta: return if unsolved, otherwise whnormalize solution.
whnormalizeNV parent gamma t@(TermMeta neutrality meta (Compose depcies) alg) ty metas reason = do
  --solution <- fromMaybe (Expr2 t) <$> awaitMeta parent ty reason meta depcies
  maybeSolution <- awaitMeta parent reason meta depcies
  case maybeSolution of
    Nothing -> case neutrality of
      MetaBlocked -> Expr2 t <$ tell [meta]
      MetaNeutral -> return $ Expr2 t
        -- neutral metas are considered whnormal, as solving them cannot trigger any computation.
    Just solution -> whnormalize parent gamma solution ty reason
{-maybeSolution <- getMeta meta depcies
  case maybeSolution of
    Nothing -> Expr2 t <$ tell [meta]
    Just solution -> whnormalize gamma solution-}
-- Wildcard: unreachable
whnormalizeNV parent gamma TermWildcard ty metas reason = unreachable
-- QName: Extract the enclosed value, turn the telescope into box-constructors and lambdas, and return.
whnormalizeNV parent gamma (TermQName qname leftDividedTelescopedVal) ty metas reason =
    let moduleMode = _leftDivided'originalMode leftDividedTelescopedVal
        telescopedVal = _leftDivided'content leftDividedTelescopedVal
        ModApplied _ quantifiedVal = telescoped2modalQuantified moduleMode telescopedVal
        quantifiedTerm = _val'term quantifiedVal
    in  whnormalize parent gamma quantifiedTerm ty reason
whnormalizeNV parent gamma (TermAlreadyChecked t ty) ty' metas reason = whnormalize parent gamma t ty' reason
-- Results annotated with an algorithm for solving them: whnormalize the result.
whnormalizeNV parent gamma (TermAlgorithm alg result) ty metas reason = whnormalize parent gamma result ty reason
-- System specific terms: call whnormalizeSys, a method of SysWHN.
whnormalizeNV parent gamma (TermSys t) ty metas reason = whnormalizeSys parent gamma t ty reason
-- Bogus terms: return them.
whnormalizeNV parent gamma t@(TermProblem _) ty metas reason = return $ Expr2 t

---------------------------

whnormalizeAST' :: forall sys whn v t .
  (SysWHN sys,
   MonadWHN sys whn,
   DeBruijnLevel v,
   MonadWriter [Int] whn,
   Analyzable sys t) => 
  Constraint sys ->
  Ctx Type sys v Void ->
  t v ->
  AnalyzerExtraInput t v ->
  Classif t v ->
  String ->
  whn (t v)
whnormalizeAST' parent gamma t extraT classifT reason =
         let attempt = subASTsTyped gamma (AnalyzerInput t extraT (ClassifWillBe classifT)) $
               \ wkn gammadelta (AnalyzerInput s extraS maybeClassifS) addressInfo ->
                 if _addressInfo'shouldWHN addressInfo
                 then whnormalizeAST parent gammadelta s extraS (fromClassifInfo unreachable maybeClassifS) reason
                 else return s
         in fromRight (return t) attempt

whnormalizeAST :: forall sys whn v t .
  (SysWHN sys,
   MonadWHN sys whn,
   DeBruijnLevel v,
   MonadWriter [Int] whn,
   Analyzable sys t) => 
  Constraint sys ->
  Ctx Type sys v Void ->
  t v ->
  AnalyzerExtraInput t v ->
  Classif t v ->
  String ->
  whn (t v)
whnormalizeAST parent gamma t extraT classifT reason =
  case analyzableToken @sys @t of
    AnTokenTerm -> whnormalize parent gamma t classifT reason
    -- also special case for AnTokenSys!
    _ -> whnormalizeAST' parent gamma t extraT classifT reason
      {-case (anErr, analyzableToken :: AnalyzableToken sys t, t) of
      (AnErrorTermMeta, AnTokenTermNV, TermMeta neutrality meta depcies alg) -> return t
      (AnErrorTermMeta, _, _) -> unreachable
      (AnErrorTermWildcard, AnTokenTermNV, TermWildcard) -> return t
      (AnErrorTermWildcard, _, _) -> unreachable
      (AnErrorTermQName, AnTokenTermNV, TermQName qname ldivVal) -> return t --_qname
      (AnErrorTermQName, _, _) -> unreachable
      (AnErrorTermAlreadyChecked, AnTokenTermNV, TermAlreadyChecked tChecked ty) -> return t
        --whnormalize parent gamma tChecked ty reason
      (AnErrorTermAlreadyChecked, _, _) -> unreachable
      (AnErrorTermAlgorithm, AnTokenTermNV, TermAlgorithm alg tResult) -> return t
        --whnormalize parent gamma tResult classifT reason
      (AnErrorTermAlgorithm, _, _) -> unreachable
      (AnErrorTermSys, AnTokenTermNV, TermSys syst) -> return t --_whnSys
      (AnErrorTermSys, _, _) -> unreachable
      (AnErrorTermProblem, AnTokenTermNV, TermProblem tProblem) -> return t
      (AnErrorTermProblem, _, _) -> unreachable
      (AnErrorVar, AnTokenTerm, Var2 v) -> return t
      (AnErrorVar, _, _) -> unreachable-}

---------------------------

{- | Either weak-head-normalizes the given term and writes nothing,
     or fails to weak-head-normalize the given term (but weak-head-normalizes as far as possible) and
     writes the indices of all metavariables that could (each in itself) unblock the situation.
-}
whnormalize :: (SysWHN sys, MonadWHN sys whn, DeBruijnLevel v, MonadWriter [Int] whn) =>
  Constraint sys ->
  Ctx Type sys v Void ->
  Term sys v ->
  Type sys v ->
  String ->
  whn (Term sys v)
-- Variable: return it
whnormalize parent gamma (Var2 v) ty reason = return $ Var2 v
-- Not a variable
whnormalize parent gamma (Expr2 t) ty reason = do
  --perform all necessary recursive calls
  (prewhnT, metas) <- listen $ whnormalizeAST' parent gamma t U1 ty reason
  --call whnormalizeNV
  whnormalizeNV parent gamma prewhnT ty metas reason

whnormalizeType :: (SysWHN sys, MonadWHN sys whn, DeBruijnLevel v, MonadWriter [Int] whn) =>
  Constraint sys ->
  Ctx Type sys v Void ->
  Type sys v ->
  String ->
  whn (Type sys v)
whnormalizeType parent gamma ty reason = whnormalizeAST parent gamma ty U1 U1 reason
