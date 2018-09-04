{-# LANGUAGE FlexibleContexts, FlexibleInstances, ApplicativeDo, MultiParamTypeClasses #-}

module Menkar.Scoper where

import Menkar.TCMonad.MonadScoper
import qualified Menkar.Raw.Syntax as Raw
import Menkar.Fine.Syntax
import Menkar.Fine.Judgement
import Control.Exception.AssertFalse

{- SEARCH FOR TODOS -}

eliminator :: MonadScoper mode modty rel sc =>
  Ctx Type mode modty v ->
  mode v ->
  Raw.Eliminator ->
  sc (SmartEliminator mode modty v)
eliminator gamma d (Raw.ElimEnd argSpec) = return $ SmartElimEnd argSpec
eliminator gamma d (Raw.ElimArg argSpec e) = do
  e' <- expr gamma d e
  return $ SmartElimArg argSpec e'
eliminator gamma d (Raw.ElimProj projSpec) = return $ SmartElimProj projSpec

expr3 :: MonadScoper mode modty rel sc =>
  Ctx Type mode modty v ->
  mode v ->
  Raw.Expr3 ->
  sc (Term mode modty v)
expr3 gamma d (Raw.ExprQName qname) = term4val gamma d qname
expr3 gamma d (Raw.ExprParens e) = expr gamma d e
expr3 gamma d (Raw.ExprNatLiteral n) = todo
expr3 gamma d (Raw.ExprImplicit) = term4newImplicit gamma d

elimination :: MonadScoper mode modty rel sc =>
  Ctx Type mode modty v ->
  mode v ->
  Raw.Elimination ->
  sc (Term mode modty v)
elimination gamma d (Raw.Elimination e elims) = do
  e' <- expr3 gamma d e
  tyE' <- type4newImplicit gamma d
  elims' <- sequenceA (eliminator gamma d <$> elims)
  result' <- term4newImplicit gamma d
  --theMode <- mode4newImplicit gamma
  pushConstraint $ Constraint {
      constraintJudgement = JudSmartElim gamma d e' tyE' elims' result',
      constraintParent = Nothing,
      constraintReason = "Scoper: Elaborate smart elimination."
    }
  return result'

expr :: MonadScoper mode modty rel sc =>
  Ctx Type mode modty v ->
  mode v ->
  Raw.Expr ->
  sc (Term mode modty v)
expr = _expr

{- TACKLE THIS THE OTHER WAY AROUND!!!
val :: MonadScoper mode modty rel s => Raw.LHS -> Raw.RHS -> s (Val mode modty v)
val lhs rhs = do
  let Raw.QNameForEntry qname = 
  return Segment {
    segmentInfo = _info,
    segmentModality = _mod,
    segmentType = _type
  }

lrEntry :: MonadScoper mode modty rel s => Raw.LREntry -> s (Entry mode modty v)
lrEntry (Raw.LREntry Raw.HeaderVal lhs rhs) = EntryVal <$> val lhs rhs
lrEntry _ = _lrentry

entry :: MonadScoper mode modty rel s => Raw.Entry -> s (Entry mode modty v)
entry (Raw.EntryLR entry) = lrEntry entry

file :: MonadScoper mode modty rel s => Raw.File -> s (Entry mode modty v)
file (Raw.File entry) = lrEntry entry
-}

