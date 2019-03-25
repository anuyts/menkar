module Menkar.TC.Segment where

import Menkar.Monad.Monad
import Menkar.Fine.Syntax
import Menkar.Fine.Context
import Menkar.Fine.Judgement
import Menkar.System.Fine

import Data.Void

checkSegment :: (MonadTC sys tc, DeBruijnLevel v) =>
  Constraint sys ->
  Ctx Type sys v Void ->
  Segment Type sys v ->
  tc ()
checkSegment parent gamma seg = do
  let dgamma' = ctx'mode gamma
  let dgamma = unVarFromCtx <$> dgamma'
  let dmu = _segment'modty seg
  let ty = _segment'content seg
  ----------
  addNewConstraint
    (JudModedModality (crispModedModality dgamma' :\\ gamma) dmu dgamma)
    (Just parent)
    "Checking the modality."
  ----------
  -- CMODE plicity (instance)
  ----------
  addNewConstraint
    (JudType (VarFromCtx <$> dmu :\\ gamma) ty)
    (Just parent)
    "Checking segment's type."

checkSegmentUni :: (MonadTC sys tc, DeBruijnLevel v) =>
  Constraint sys ->
  Ctx Type sys v Void ->
  Segment Type sys v ->
  tc ()
checkSegmentUni parent gamma seg = do
  let dgamma' = ctx'mode gamma
  let dgamma = unVarFromCtx <$> dgamma'
  let dmu = _segment'modty seg
  let ty = _segment'content seg
  ----------
  addNewConstraint
    (JudModedModality (crispModedModality dgamma' :\\ gamma) dmu dgamma)
    (Just parent)
    "Checking the modality."
  ----------
  -- CMODE plicity (instance)
  ----------
  addNewConstraint
    (JudTerm (VarFromCtx <$> dmu :\\ gamma) (unType ty) (hs2type $ UniHS dgamma))
    (Just parent)
    "Type-checking segment's type."
