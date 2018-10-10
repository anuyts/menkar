module Menkar.TypeChecker where

import Menkar.Fine.Syntax
import Menkar.Fine.Substitution
import Menkar.Fine.Context
import Menkar.Fine.Context.Variable
import Menkar.Fine.Judgement
import qualified Menkar.Raw.Syntax as Raw
import Menkar.TCMonad.MonadTC

-- CMODE means you need to check a mode
-- CMODTY means you need to check a modality

checkConstraint :: MonadTC mode modty rel tc => Constraint mode modty rel -> tc ()
checkConstraint constraint = case constraint'judgement constraint of
{-JudCtx gamma d -> case gamma of
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
            "Type of last variable in context."
            i
    seg :^^ gamma2 -> tcFail $ "For now, left extension of context is not supported by the type-checker."
    gamma2 :<...> modul -> 
    _ -> _checkJudCtx-} -- contexts start empty and grow only in well-typed ways.
  _ -> _checkConstraint
