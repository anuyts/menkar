module Menkar.TC.Inference.Entry where

import Menkar.TC.Monad
import Menkar.Fine.Syntax
import Menkar.Fine.Context
import Menkar.Fine.Judgement

import Data.Void
import Data.Foldable
import Data.Functor.Compose
import Control.Monad.State.Lazy

checkSegment :: (MonadTC mode modty rel tc, DeBruijnLevel v) =>
  Constraint mode modty rel ->
  Ctx Type mode modty v Void ->
  Segment Type mode modty v ->
  tc ()
checkSegment parent gamma seg = do
  let dmu = _segment'modty seg
  let ty = _segment'content seg
  -- CMODE mode/modality
  -- CMODE plicity (instance)
  addNewConstraint
    (JudType (VarFromCtx <$> dmu :\\ gamma) ty)
    (Just parent)
    "Checking segment's type."

checkTelescoped :: (MonadTC mode modty rel tc, DeBruijnLevel v) =>
  ( forall w .
    (DeBruijnLevel w) =>
    Ctx Type mode modty w Void ->
    rhs mode modty w ->
    tc ()
  ) ->
  Constraint mode modty rel ->
  Ctx Type mode modty v Void ->
  Telescoped Type rhs mode modty v ->
  tc ()
checkTelescoped checkRHS parent gamma (Telescoped rhs) = checkRHS gamma rhs
checkTelescoped checkRHS parent gamma (seg :|- telescopedRHS) = do
  addNewConstraint
    (JudSegment gamma seg)
    (Just parent)
    "Checking an assumption."
  checkTelescoped checkRHS parent (gamma :.. VarFromCtx <$> seg) telescopedRHS
checkTelescoped checkRHS parent gamma (dmu :** telescopedRHS) = do
  -- CMODE dmu
  checkTelescoped checkRHS parent (VarFromCtx <$> dmu :\\ gamma) telescopedRHS

-------------------------

checkValRHS :: (MonadTC mode modty rel tc, DeBruijnLevel v) =>
  Constraint mode modty rel ->
  Ctx Type mode modty v Void ->
  ValRHS mode modty v ->
  tc ()
checkValRHS parent gamma valRHS = do
  addNewConstraint
    (JudType gamma (_val'type valRHS))
    (Just parent)
    "Checking type of RHS."
  addNewConstraint
    (JudTerm gamma (_val'term valRHS) (_val'type valRHS))
    (Just parent)
    "Type-checking RHS."

checkModuleRHS :: (MonadTC mode modty rel tc, DeBruijnLevel v) =>
  Constraint mode modty rel ->
  Ctx Type mode modty v Void ->
  ModuleRHS mode modty v ->
  tc ()
checkModuleRHS parent gamma (ModuleRHS (Compose entries)) =
  flip evalStateT [] $ sequenceA_ $ flip fmap (reverse entries) $ \ entry -> do
    prevEntries <- get
    lift $ checkEntry parent (gamma :<...> ModuleRHS (Compose prevEntries)) entry
    put $ (fmap VarFromCtx <$> entry) : prevEntries
  --sequenceA_ $ checkEntry parent (gamma :<...> _modul) <$> reverse entries

-------------------------

checkVal :: (MonadTC mode modty rel tc, DeBruijnLevel v) =>
  Constraint mode modty rel ->
  Ctx Type mode modty v Void ->
  Val mode modty v ->
  tc ()
checkVal parent gamma val = do
  -- CMODE plicity (instance)
  -- CMODE mode/modality
  checkTelescoped (checkValRHS parent) parent gamma (_decl'content val)

checkModule :: (MonadTC mode modty rel tc, DeBruijnLevel v) =>
  Constraint mode modty rel ->
  Ctx Type mode modty v Void ->
  Module mode modty v ->
  tc ()
checkModule parent gamma modul = do
  -- CMODE plicity (instance)
  -- CMODE mode modality
  checkTelescoped (checkModuleRHS parent) parent gamma (_decl'content modul)

checkEntry :: (MonadTC mode modty rel tc, DeBruijnLevel v) =>
  Constraint mode modty rel ->
  Ctx Type mode modty v Void ->
  Entry mode modty v ->
  tc ()
checkEntry parent gamma entry = do
  let (jud, reason) = case entry of
        EntryVal val -> (JudVal gamma val, "Checking val.")
        EntryModule modul -> (JudModule gamma modul, "Checking module.")
  addNewConstraint jud (Just parent) reason
  --constraint <- defConstraint jud (Just parent) reason
  --selfcontained constraint $ addConstraint constraint
{-
checkEntry parent gamma (EntryVal val) =
  addNewConstraint (JudVal gamma val) (Just parent) "Checking val."
checkEntry parent gamma (EntryModule modul) =
  addNewConstraint (JudModule gamma modul) (Just parent) "Checking module."
-}
