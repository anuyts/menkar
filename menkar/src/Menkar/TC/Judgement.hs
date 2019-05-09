module Menkar.TC.Judgement where

import Menkar.System
import Menkar.Fine.Syntax
import Menkar.Basic.Context
import Menkar.Fine.Context
import Menkar.Fine.Judgement
import Menkar.Fine.LookupQName
import qualified Menkar.Raw.Syntax as Raw
import Menkar.Monad.Monad
import Control.Exception.AssertFalse
import Menkar.TC.AST
--import Menkar.TC.Term
import Menkar.TC.SmartElim
--import Menkar.TC.Rel
--import Menkar.TC.Entry
--import Menkar.TC.Segment
--import Menkar.TC.Solve
import Menkar.WHN

import Data.Void
import Control.Lens
import Data.Functor.Compose
import Control.Monad
import Control.Monad.Writer.Lazy

checkConstraint ::
  (SysTC sys, MonadTC sys tc) =>
  Constraint sys -> tc ()
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

  Jud token gamma t extraT classifT -> void $ checkAST parent gamma t extraT classifT

  JudRel token eta rel gamma (Twice1 t1 t2) maybeCTs -> _checkASTRel eta rel gamma t1 t2 maybeCTs

  {-
  JudType gamma (Type ty) -> do
    {-lvl <- newMetaTerm
             (Just parent)
             topDeg
             (ModedModality dataMode irrMod :\\ gamma)
             (Type $ Expr2 $ TermCons $ ConsUniHS $ NatType)
             "Infer universe level of type."-}
    addNewConstraint
      (JudTerm gamma ty (hs2type $ UniHS (unVarFromCtx <$> ctx'mode gamma) {-lvl-}))
      (Just parent)
      "Checking that type lives in a Hofmann-Streicher universe."

  JudTypeRel deg gamma (Twice2 ty1 ty2) -> do
    let dgamma = unVarFromCtx <$> ctx'mode gamma
    checkTypeRel parent (ModedDegree dgamma deg) gamma ty1 ty2

  JudTerm gamma t ty -> checkTerm parent gamma t ty

  JudTermRel eta deg gamma (Twice2 t1 t2) (Twice2 ty1 ty2) -> do
    let dgamma = unVarFromCtx <$> ctx'mode gamma
    checkTermRel parent eta (ModedDegree dgamma deg) gamma t1 t2 ty1 ty2
  -}

  JudEta gamma t tyT -> case t of
    Expr2 (TermMeta MetaBlocked meta (Compose depcies) maybeAlg) -> do
      maybeT <- awaitMeta parent "If it's solved, then I needn't bother." meta depcies
      case maybeT of
        Nothing -> void $ _checkEta parent gamma t tyT
        Just _ -> return () -- every known term is obviously equal to its eta-expansion.
    _ -> unreachable

  JudSmartElim gamma eliminee tyEliminee eliminators result tyResult ->
    checkSmartElim parent gamma eliminee tyEliminee eliminators result tyResult

  -- keep this until the end of time
  JudGoal gamma goalname t tyT -> tcReport parent "This isn't my job; delegating to a human."

  JudResolve gamma t ty -> todo

  {-
  JudMode gamma d -> checkMode parent gamma d
  
  JudModeRel gamma d1 d2 -> checkModeRel parent gamma d1 d2
  
  JudModality gamma mu ddom dcod -> checkModality parent gamma mu ddom dcod
  
  JudModalityRel modrel gamma mu1 mu2 ddom dcod -> checkModalityRel parent modrel gamma mu1 mu2 ddom dcod

  JudModedModality gamma (ModedModality ddom mu) dcod -> do
    addNewConstraint (JudMode gamma ddom) (Just parent) "Checking the mode."
    addNewConstraint (JudModality gamma mu ddom dcod) (Just parent) "Checking the modality."

  JudModedModalityRel modrel gamma (ModedModality ddom1 mu1) (ModedModality ddom2 mu2) dcod -> do
    addNewConstraint (JudModeRel gamma ddom1 ddom2) (Just parent) "Relating modes."
    addNewConstraint (JudModalityRel modrel gamma mu1 mu2 ddom1 dcod) (Just parent) "Relating modalities."
  -}

  JudSys jud -> checkSysJudgement parent jud

  {-
  JudSegment gamma seg -> checkSegment parent gamma seg

  JudVal gamma val -> checkVal parent gamma val

  JudModule gamma modul -> checkModule parent gamma modul

  JudEntry gamma entry -> checkEntry parent gamma entry
  -}
  --_ -> _checkConstraint
