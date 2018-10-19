module Menkar.TypeChecker where

import Menkar.Fine.Syntax
import Menkar.Fine.Substitution
import Menkar.Fine.Context
import Menkar.Fine.Context.Variable
import Menkar.Fine.Judgement
import qualified Menkar.Raw.Syntax as Raw
import Menkar.TCMonad.MonadTC
import Data.Void

-- CMODE means you need to check a mode
-- CMODTY means you need to check a modality

checkConstraintTerm :: MonadTC mode modty rel tc =>
    Ctx Type mode modty v Void ->
    mode v ->
    Term mode modty v ->
    Type mode modty v ->
    tc ()

checkConstraintTerm gamma d (Var3 v) (Type ty) = _checkVar

checkConstraintTerm gamma d t (Type ty) = _checkConstraintTerm

-------

checkConstraint :: MonadTC mode modty rel tc => Constraint mode modty rel -> tc ()

checkConstraint parent = case constraint'judgement parent of
  
  {-
  JudCtx gamma d -> case gamma of
    CtxEmpty -> return ()
    gamma2 :.. seg -> do
      let ty = _decl'content seg
      let ModedModality d2 mu = _decl'modty seg
      let gamma3 = ModedContramodality d mu :\\ gamma2
      i <- newConstraintID
      -- CMODE b\gamma d2
      -- CMODTY b\gamma mu
      addConstraint $ Constraint
            (JudType gamma3 d2 ty)
            constraint
            "Checking type of last variable in context."
            i
    seg :^^ gamma2 -> tcFail $ "For now, left extension of context is not supported by the type-checker."
    gamma2 :<...> modul -> 
    _ -> _checkJudCtx
  -} -- contexts start empty and grow only in well-typed ways.

  JudType gamma d (Type ty) -> do
    lvl <- term4newImplicit gamma
    i <- id4newConstraint
    addConstraint $ Constraint
      (JudTerm gamma d ty (Type $ Expr3 $ TermCons $ ConsUniHS $ UniHS d lvl))
      (Just parent)
      "Checking that type lives in a Hofmann-Streicher universe."
      i

  JudTerm gamma d t ty -> checkConstraintTerm gamma d t ty
  
  _ -> _checkConstraint
