module Menkar.TC.Inference where

import Menkar.Fine.Syntax
import Menkar.Basic.Context
import Menkar.Fine.Context
import Menkar.Fine.Judgement
import Menkar.Fine.Multimode
import Menkar.Fine.LookupQName
import qualified Menkar.Raw.Syntax as Raw
import Menkar.TC.Monad
import Data.Void

-- CMODE means you need to check a mode
-- CMODTY means you need to check a modality

checkConstraintTerm :: MonadTC mode modty rel tc =>
    Ctx Type mode modty v Void ->
    Term mode modty v ->
    Type mode modty v ->
    tc ()

checkConstraintTerm gamma (Var3 v) (Type ty) = do
  let ldivseg = lookupVar gamma v
  _checkVar

checkConstraintTerm gamma t (Type ty) = _checkConstraintTerm

-------

checkConstraint :: Multimode mode modty => MonadTC mode modty rel tc => Constraint mode modty rel -> tc ()

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

  JudType gamma (Type ty) -> do
    lvl <- term4newImplicit gamma
    i <- newConstraintID
    addConstraint $ Constraint
      (JudTerm gamma ty (Type $ Expr3 $ TermCons $ ConsUniHS $ UniHS (unVarFromCtx <$> ctx'mode gamma) lvl))
      (Just parent)
      "Checking that type lives in a Hofmann-Streicher universe."
      i

  JudTerm gamma t ty -> checkConstraintTerm gamma t ty
  
  _ -> _checkConstraint
