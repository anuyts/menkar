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
  Raw.Eliminator ->
  sc (SmartEliminator mode modty v)
eliminator gamma (Raw.ElimEnd argSpec) = return $ SmartElimEnd argSpec
eliminator gamma (Raw.ElimArg argSpec e) = do
  e' <- todo
  return $ SmartElimArg argSpec e'
eliminator gamma (Raw.ElimProj projSpec) = return $ SmartElimProj projSpec

expr3 :: MonadScoper mode modty rel sc =>
  Ctx Type mode modty v ->
  Raw.Expr3 ->
  sc (Term mode modty v)
expr3 gamma e = _


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

