{-# LANGUAGE UndecidableInstances #-}

module Menkar.Monad.Monad where

import Menkar.System.Fine
import Menkar.Fine.Syntax
import Menkar.Fine.Judgement
import Menkar.Fine.Context
import qualified Menkar.Raw.Syntax as Raw 
--import Menkar.Scoper.Monad

import Data.Void
import Control.Monad.Trans.Class
import Data.Functor.Compose
import Control.Monad.Trans.Maybe
import Control.Monad.Fail
import Data.Kind hiding (Type, Constraint)

data Constraint sys = Constraint {
    constraint'judgement :: Judgement sys,
    constraint'parent :: Maybe (Constraint sys),
    constraint'reason :: String,
    constraint'id :: Int
  }

class (
    MonadFail sc,
    Degrees sys
  ) => MonadScoper
    (sys :: KSys)
    (sc :: * -> *)
    | sc -> sys where
  {-| After scoping, before type-checking, metas are put to sleep.
      They awake as soon as the type-checker tries to query one.

      @'newMetaTermNoCheck'@ should only be used when you are sure the meta will be type-checked (in a term judgement)
      later on.
  -}
  newMetaTermNoCheck :: (DeBruijnLevel v) =>
    Maybe (Constraint sys)
    -- -> Degree sys v {-^ Degree up to which it should be solved -}
    -> Ctx Type sys v Void
    -> MetaNeutrality
    -> Maybe (Algorithm sys v)
    -> String
    -> sc (Term sys v)
  scopeFail :: String -> sc a

instance (MonadScoper sys sc, MonadTrans mT, MonadFail (mT sc)) => MonadScoper sys (mT sc) where
  newMetaTermNoCheck maybeParent gamma etaFlag maybeAlg reason =
    lift $ newMetaTermNoCheck maybeParent gamma etaFlag maybeAlg reason
  scopeFail msg = lift $ scopeFail msg

class (
    Degrees sys,
    MonadScoper sys whn
  ) => MonadWHN sys whn | whn -> sys where
  {-| Returns the meta's solution if the meta has been solved.
      Otherwise, returns @Nothing@. Then you have two options:
      1) Deal with it.
      2) Block. In this case, the continuation as of this point is saved as being blocked on this meta.
         (If other earlier or future metas were also unsuccessfully queried, then the continuations from those points
         are also saved.) The first time a meta is solved that contributed to this blockade, its continuation will be
         run with the soluiton.
      It is an error to await the same meta twice. -}
  awaitMeta :: Constraint sys -> String -> Int -> [Term sys v] -> whn (Maybe (Term sys v))

class (
    Degrees sys,
    MonadWHN sys tc
  ) => MonadTC sys tc | tc -> sys where
  --term4newImplicit :: Ctx ty sys v Void -> tc (Term sys v)
  --mode4newImplicit :: Ctx ty sys v Void -> tc (mode v)
  --modty4newImplicit :: Ctx ty sys v Void -> tc (modty v)
  --genVarName :: tc Raw.Name
  --newConstraintID :: tc Int
  {-| Create and register a new constraint. -}
  defConstraint ::
    Judgement sys ->
    Maybe (Constraint sys) ->
    String ->
    tc (Constraint sys)
  {-| Add a check for this constraint to the task stack. -}
  addConstraint :: Constraint sys -> tc ()
  addNewConstraint ::
    Judgement sys ->
    Maybe (Constraint sys) ->
    String ->
    tc()
  {-| For instances. Will only be considered if all nice constraints have been considered. -}
  addConstraintReluctantly :: Constraint sys -> tc ()
  {-| Provide a solution for the meta. All continuations thus unblocked are added to the task stack. -}
  solveMeta ::
    Constraint sys ->
    Int ->
    (forall tc' v .
      (MonadTC sys tc', Eq v, DeBruijnLevel v) =>
      Ctx Type sys v Void ->
      tc' (Term sys v)
    ) -> tc ()
  --{-| Returns the value of the meta, if existent. Awakens the scoper-induced meta if still asleep.
  ---}
  --getMeta :: Int -> [Term sys v] -> tc (Maybe (Term sys v))
  --{-| Shove a judgement aside; it will only be reconsidered when one of the given metas has been solved. -}
  --blockOnMetas :: [Int] -> Constraint sys -> tc ()
  {-| Aborts (rather than cancels) computation.
      For every call to @'awaitMeta'@ that didn't yield a result, the continuation as of that point
      is saved. The first time one of the corresponding metas is resolved, the continuation from that point will be run. -}
  tcBlock :: Constraint sys -> String -> tc a
  tcReport :: Constraint sys -> String -> tc ()
  tcFail :: Constraint sys -> String -> tc a
  --leqMod :: Modality sys v -> Modality sys v -> tc Bool
  -- | DO NOT USE @'awaitMeta'@ WITHIN!
  --selfcontained :: Constraint sys -> tc () -> tc ()

await :: (MonadWHN sys whn) =>
  Constraint sys -> String -> Term sys v -> whn (Maybe (Term sys v))
await parent reason (Expr2 (TermMeta flagEta meta (Compose depcies) alg)) = runMaybeT $ do
  term <- MaybeT $ awaitMeta parent reason meta depcies
  MaybeT $ await parent reason term
await parent reason t = return $ Just t

{-
addNewConstraint :: MonadTC sys tc =>
  Judgement sys ->
  Maybe (Constraint sys) ->
  String ->
  tc()
addNewConstraint judgement parent reason = addConstraint =<< defConstraint judgement parent reason
-}

-- | Not to be used by the Scoper.
-- | No eta flag is given: it is set to @False@, as there is no eta-equality in the universe.
-- | No algorithm is given: this isn't used by the scoper anyway.
newMetaTerm :: (MonadTC sys tc, DeBruijnLevel v) =>
  Maybe (Constraint sys) ->
  Ctx Type sys v Void ->
  Type sys v ->
  MetaNeutrality ->
  String ->
  tc (Term sys v)
newMetaTerm maybeParent gamma ty neutrality reason = do
  t <- newMetaTermNoCheck maybeParent gamma neutrality Nothing reason
  addNewConstraint
    (JudTerm gamma t ty)
    maybeParent
    reason
  {- --The term judgement will trigger eta-expansion.
  addNewConstraint
    (JudEta gamma t ty)
    maybeParent
    (reason ++ " (eta-expansion)")
  -}
  return t

-- | Not to be used by the Scoper.
-- | No eta flag is given: it is set to @False@, as there is no eta-equality in the universe.
-- | No algorithm is given: this isn't used by the scoper anyway.
newMetaType :: (MonadTC sys tc, DeBruijnLevel v) =>
  Maybe (Constraint sys) ->
  Ctx Type sys v Void ->
  String ->
  tc (Type sys v)
newMetaType maybeParent gamma reason = do
  t <- Type <$> newMetaTermNoCheck maybeParent gamma MetaBlocked Nothing reason
  addNewConstraint
    (JudType gamma t)
    maybeParent
    reason
  return t

-- | Not to be used by the Scoper.
-- | No eta flag is given: it is set to @False@, as there is no eta-equality in the universe.
-- | No algorithm is given: this isn't used by the scoper anyway.
newMetaTypeRel :: (MonadTC sys tc, DeBruijnLevel v) =>
  Maybe (Constraint sys) ->
  Degree sys v ->
  Ctx (Twice2 Type) sys v Void ->
  Type sys v ->
  String ->
  tc (Type sys v)
newMetaTypeRel maybeParent deg gamma ty2 reason = do
  ty1 <- Type <$> newMetaTermNoCheck maybeParent (fstCtx gamma) MetaBlocked Nothing reason
  addNewConstraint
    (JudTypeRel deg gamma (Twice2 ty1 ty2))
    maybeParent
    reason
  return ty1

{-
instance (MonadTC sys tc, MonadTrans mT, Monad (mT tc)) =>
  MonadTC sys (mT tc) where
  --term4newImplicit gamma = lift $ term4newImplicit gamma
  --mode4newImplicit gamma = lift $ mode4newImplicit gamma
  --modty4newImplicit gamma = lift $ modty4newImplicit gamma
  --genVarName = lift $ genVarName
  newConstraintID = lift $ newConstraintID
  addConstraint c = lift $ addConstraint c
  addConstraintReluctantly c = lift $ addConstraintReluctantly c
  solveMeta parent meta solver = lift $ solveMeta parent meta solver
  --getMeta meta depcies = lift $ getMeta meta depcies
  --blockOnMetas metas c = lift $ blockOnMetas metas c
  awaitMeta parent reason meta depcies = lift $ awaitMeta parent reason meta depcies
  tcBlock msg = lift $ tcBlock msg
  tcFail c msg = lift $ tcFail c msg
  tcReport c msg = lift $ tcReport c msg
  leqMod mu nu = lift $ leqMod mu nu
-}
