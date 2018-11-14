module Menkar.TC.Inference where

import Menkar.Fine.Syntax
import Menkar.Basic.Context
import Menkar.Fine.Context
import Menkar.Fine.Judgement
import Menkar.Fine.Multimode
import Menkar.Fine.LookupQName
import qualified Menkar.Raw.Syntax as Raw
import Menkar.TC.Monad
import Control.Exception.AssertFalse
import Menkar.TC.Inference.Term

import Data.Void
import Control.Lens
import Data.Functor.Compose
import Control.Monad

-- CMODE means you need to check a mode
-- CMODTY means you need to check a modality

-------

checkEta :: (MonadTC mode modty rel tc) =>
  Constraint mode modty rel ->
  Ctx Type mode modty v Void ->
  Term mode modty v ->
  Type mode modty v ->
  tc ()
checkEta parent gamma t tyT = _checkEta

-------
-- ================================================================================================
-------

checkConstraint :: (MonadTC mode modty rel tc) => Constraint mode modty rel -> tc ()

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
    addNewConstraint
      (JudTerm gamma ty (Type $ Expr3 $ TermCons $ ConsUniHS $ UniHS (unVarFromCtx <$> ctx'mode gamma) lvl))
      (Just parent)
      "Checking that type lives in a Hofmann-Streicher universe."

  JudTerm gamma t ty -> checkTerm parent gamma t ty

  JudEta gamma t tyT -> checkEta parent gamma t tyT

  -- keep this until the end of time
  JudGoal gamma goalname t tyT -> blockOnMetas [] parent
  
  _ -> _checkConstraint
