{-# LANGUAGE UndecidableInstances #-}

module Menkar.TC.Monad.Monad where

import Menkar.Fine.Syntax
import Menkar.Fine.Judgement
import Menkar.Fine.Context
import Menkar.Fine.Multimode
import qualified Menkar.Raw.Syntax as Raw
--import Menkar.Scoper.Monad

import Data.Void
import Control.Monad.Trans.Class
import Data.Functor.Compose
import Control.Monad.Trans.Maybe

data Constraint mode modty rel = Constraint {
    constraint'judgement :: Judgement mode modty rel,
    constraint'parent :: Maybe (Constraint mode modty rel),
    constraint'reason :: String,
    constraint'id :: Int
  }

class (
    Monad sc,
    Traversable mode,
    Traversable modty,
    Traversable rel,
    Degrees mode modty rel
  ) => MonadScoper
    (mode :: * -> *)
    (modty :: * -> *)
    (rel :: * -> *)
    (sc :: * -> *)
    | sc -> mode, sc -> modty, sc -> rel where
  annot4annot :: (DeBruijnLevel v) => Ctx Type mode modty v Void -> 
    Raw.Qualified String -> [SmartEliminator mode modty v] -> sc (Annotation mode modty v)
  {-| After scoping, before type-checking, metas are put to sleep.
      They awake as soon as the type-checker tries to query one.

      @'newMetaTermNoCheck'@ should only be used when you are sure the meta will be type-checked (in a term judgement)
      later on.
  -}
  newMetaTermNoCheck :: (DeBruijnLevel v) =>
    Maybe (Constraint mode modty rel)
    -> rel v {-^ Degree up to which it should be solved -}
    -> Ctx Type mode modty v Void -> String -> sc (Term mode modty v)
  newMetaMode ::
    Maybe (Constraint mode modty rel) -> Ctx Type mode modty v Void -> String -> sc (mode v)
  newMetaModty ::
    Maybe (Constraint mode modty rel) -> Ctx Type mode modty v Void -> String -> sc (modty v)
  scopeFail :: String -> sc a

instance (MonadScoper mode modty rel sc, MonadTrans mT, Monad (mT sc)) => MonadScoper mode modty rel (mT sc) where
  annot4annot gamma qstring args = lift $ annot4annot gamma qstring args
  newMetaTermNoCheck maybeParent deg gamma reason = lift $ newMetaTermNoCheck maybeParent deg gamma reason
  newMetaMode maybeParent gamma reason = lift $ newMetaMode maybeParent gamma reason
  newMetaModty maybeParent gamma reason = lift $ newMetaModty maybeParent gamma reason
  scopeFail msg = lift $ scopeFail msg

class (
    Degrees mode modty rel,
    MonadScoper mode modty rel tc
  ) => MonadTC mode modty rel tc | tc -> mode, tc -> modty, tc -> rel where
  --term4newImplicit :: Ctx ty mode modty v Void -> tc (Term mode modty v)
  --mode4newImplicit :: Ctx ty mode modty v Void -> tc (mode v)
  --modty4newImplicit :: Ctx ty mode modty v Void -> tc (modty v)
  --genVarName :: tc Raw.Name
  newConstraintID :: tc Int
  addConstraint :: Constraint mode modty rel -> tc ()
  {-| For instances. Will only be considered if all nice constraints have been considered. -}
  addConstraintReluctantly :: Constraint mode modty rel -> tc ()
  solveMeta :: Int -> (forall tc' v .
    (MonadTC mode modty rel tc', Eq v, DeBruijnLevel v) =>
    Ctx Type mode modty v Void ->
    tc' (Term mode modty v)
    ) -> tc ()
  --{-| Returns the value of the meta, if existent. Awakens the scoper-induced meta if still asleep.
  ---}
  --getMeta :: Int -> [Term mode modty v] -> tc (Maybe (Term mode modty v))
  --{-| Shove a judgement aside; it will only be reconsidered when one of the given metas has been solved. -}
  --blockOnMetas :: [Int] -> Constraint mode modty rel -> tc ()
  {-| Forks computation, once returning nothing and once returning the meta's value.
      The branch that gets nothing is run immediately. If it blocks by calling @'tcBlock'@,
      then the other branch is called when the meta is resolved. -}
  awaitMeta :: Constraint mode modty rel -> String -> Int -> [Term mode modty v] -> tc (Maybe (Term mode modty v))
  tcBlock :: String -> tc a
  tcReport :: Constraint mode modty rel -> String -> tc ()
  tcFail :: Constraint mode modty rel -> String -> tc a
  leqMod :: modty v -> modty v -> tc Bool

await :: (MonadTC mode modty rel tc) =>
  Constraint mode modty rel -> String -> Term mode modty v -> tc (Maybe (Term mode modty v))
await parent reason (Expr3 (TermMeta meta (Compose depcies))) = runMaybeT $ do
  term <- MaybeT $ awaitMeta parent reason meta depcies
  MaybeT $ await parent reason term
await parent reason t = return $ Just t

addNewConstraint :: MonadTC mode modty rel tc =>
  Judgement mode modty rel ->
  Maybe (Constraint mode modty rel) ->
  String ->
  tc()
addNewConstraint judgement parent reason = do
  i <- newConstraintID
  addConstraint $ Constraint judgement parent reason i

-- | Not to be used by the Scoper.
newMetaTerm :: (MonadTC mode modty rel tc, DeBruijnLevel v) =>
  Maybe (Constraint mode modty rel) ->
  rel v ->
  Ctx Type mode modty v Void ->
  Type mode modty v ->
  String ->
  tc (Term mode modty v)
newMetaTerm maybeParent deg gamma ty reason = do
  t <- newMetaTermNoCheck maybeParent deg gamma reason
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
newMetaType :: (MonadTC mode modty rel tc, DeBruijnLevel v) =>
  Maybe (Constraint mode modty rel) ->
  rel v ->
  Ctx Type mode modty v Void ->
  String ->
  tc (Type mode modty v)
newMetaType maybeParent deg gamma reason = do
  t <- Type <$> newMetaTermNoCheck maybeParent deg gamma reason
  addNewConstraint
    (JudType gamma t)
    maybeParent
    reason
  return t

-- | Not to be used by the Scoper.
newMetaTypeRel :: (MonadTC mode modty rel tc, DeBruijnLevel v) =>
  Maybe (Constraint mode modty rel) ->
  rel v ->
  Ctx (Pair3 Type) mode modty v Void ->
  Type mode modty v ->
  String ->
  tc (Type mode modty v)
newMetaTypeRel maybeParent deg gamma ty2 reason = do
  ty1 <- Type <$> newMetaTermNoCheck maybeParent deg (fstCtx gamma) reason
  addNewConstraint
    (JudTypeRel deg gamma (Pair3 ty1 ty2))
    maybeParent
    reason
  return ty1

newMetaModedModality :: MonadScoper mode modty rel tc =>
  Maybe (Constraint mode modty rel) ->
  Ctx Type mode modty v Void ->
  String ->
  tc (ModedModality mode modty v)
newMetaModedModality parent gamma reason = do
  d <- newMetaMode parent gamma reason
  mu <- newMetaModty parent gamma reason
  return $ ModedModality d mu

instance (MonadTC mode modty rel tc, MonadTrans mT, Monad (mT tc)) =>
  MonadTC mode modty rel (mT tc) where
  --term4newImplicit gamma = lift $ term4newImplicit gamma
  --mode4newImplicit gamma = lift $ mode4newImplicit gamma
  --modty4newImplicit gamma = lift $ modty4newImplicit gamma
  --genVarName = lift $ genVarName
  newConstraintID = lift $ newConstraintID
  addConstraint c = lift $ addConstraint c
  addConstraintReluctantly c = lift $ addConstraintReluctantly c
  solveMeta meta solver = lift $ solveMeta meta solver
  --getMeta meta depcies = lift $ getMeta meta depcies
  --blockOnMetas metas c = lift $ blockOnMetas metas c
  awaitMeta parent reason meta depcies = lift $ awaitMeta parent reason meta depcies
  tcBlock msg = lift $ tcBlock msg
  tcFail c msg = lift $ tcFail c msg
  tcReport c msg = lift $ tcReport c msg
  leqMod mu nu = lift $ leqMod mu nu
