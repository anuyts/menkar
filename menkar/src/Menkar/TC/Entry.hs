module Menkar.TC.Entry where

import Menkar.System.Fine
import Menkar.Monad.Monad
import Menkar.Fine.Syntax
import Menkar.Fine.Context
import Menkar.Fine.Judgement
import Menkar.TC.Segment

import Data.Void
import Data.Foldable
import Data.Functor.Compose
import Data.List (inits)
import Control.Monad.State.Lazy

checkTelescoped :: (MonadTC sys tc, DeBruijnLevel v) =>
  ( forall w .
    (DeBruijnLevel w) =>
    Ctx Type sys w Void ->
    rhs sys w ->
    tc ()
  ) ->
  Constraint sys ->
  Ctx Type sys v Void ->
  Telescoped Type rhs sys v ->
  tc ()
checkTelescoped checkRHS parent gamma (Telescoped rhs) = checkRHS gamma rhs
checkTelescoped checkRHS parent gamma (seg :|- telescopedRHS) = do
  addNewConstraint
    (JudSegment gamma seg)
    (Just parent)
    "Checking an assumption."
  checkTelescoped checkRHS parent (gamma :.. VarFromCtx <$> seg) telescopedRHS
checkTelescoped checkRHS parent gamma (dmu :** telescopedRHS) = do
  addNewConstraint
    (JudModedModality (crispModedModality :\\ gamma) dmu (unVarFromCtx <$> ctx'mode gamma))
    (Just parent)
    "Checking a modality (though I'm a bit surprised that I have to do this, as there is no syntax for it...)."
  checkTelescoped checkRHS parent (VarFromCtx <$> dmu :\\ gamma) telescopedRHS

-------------------------

checkValRHS :: (MonadTC sys tc, DeBruijnLevel v) =>
  Constraint sys ->
  Ctx Type sys v Void ->
  ValRHS sys v ->
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

checkModuleRHS :: (MonadTC sys tc, DeBruijnLevel v) =>
  Constraint sys ->
  Ctx Type sys v Void ->
  ModuleRHS sys v ->
  tc ()
checkModuleRHS parent gamma (ModuleRHS (Compose entries)) =
  forM_ revEntriesWithPreds $ \ (entry, prevEntries) -> do
    checkEntry parent (gamma :<...> ModuleRHS (Compose prevEntries)) entry
  where revEntries = reverse entries
        revEntries' = fmap (fmap (fmap VarFromCtx)) revEntries
        revEntriesWithPreds = zip revEntries (inits revEntries')
          {- [(entry1, []),
              (entry2, [entry1]),
              (entry3, [entry1, entry2]),
              ...
             ]
          -}

-------------------------

checkVal :: (MonadTC sys tc, DeBruijnLevel v) =>
  Constraint sys ->
  Ctx Type sys v Void ->
  Val sys v ->
  tc ()
checkVal parent gamma val = do
  -- CMODE plicity (instance)
  -- CMODE mode/modality
  checkTelescoped (checkValRHS parent) parent gamma (_decl'content val)

checkModule :: (MonadTC sys tc, DeBruijnLevel v) =>
  Constraint sys ->
  Ctx Type sys v Void ->
  Module sys v ->
  tc ()
checkModule parent gamma modul = do
  -- CMODE plicity (instance)
  -- CMODE mode modality
  checkTelescoped (checkModuleRHS parent) parent gamma (_decl'content modul)

checkEntry :: (MonadTC sys tc, DeBruijnLevel v) =>
  Constraint sys ->
  Ctx Type sys v Void ->
  Entry sys v ->
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
