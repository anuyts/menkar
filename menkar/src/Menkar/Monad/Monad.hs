{-# LANGUAGE UndecidableInstances #-}

module Menkar.Monad.Monad where

import Menkar.ID
import Menkar.System.Fine
import Menkar.Fine.Syntax
import Menkar.Fine.Judgement
import Menkar.Fine.Context
import qualified Menkar.Raw.Syntax as Raw
import Menkar.Analyzer
--import Menkar.Scoper.Monad

import Data.Void
import Control.Monad.Trans.Class
import Data.Functor.Compose
import Control.Monad.Trans.Maybe
import Control.Monad.Fail
import Data.Kind hiding (Type, Constraint)
import GHC.Generics

data Constraint sys = Constraint {
    _constraint'judgement :: Judgement sys,
    _constraint'parent :: Maybe (Constraint sys),
    _constraint'reason :: String,
    _constraint'id :: Int
  }

data PriorityConstraint = PriorityDefault | PriorityFork | PriorityEta deriving (Eq, Ord)
getJudgementPriority :: Judgement sys -> PriorityConstraint
getJudgementPriority (JudEta token gamma t extraT ct) = PriorityEta
getJudgementPriority _ = PriorityDefault
getConstraintPriority :: Constraint sys -> PriorityConstraint
getConstraintPriority = getJudgementPriority . _constraint'judgement

class (
    MonadFail sc,
    Degrees sys
  ) => MonadScoper
    (sys :: KSys)
    (sc :: * -> *)
    | sc -> sys where
  newMetaID :: (DeBruijnLevel v) => Ctx Type sys v -> String -> sc (Int, [(Mode sys :*: Term sys) v])
  scopeFail :: String -> sc a

  {-| After scoping, before type-checking, metas are put to sleep.
      They awake as soon as the type-checker tries to query one.

      @'newMetaTermNoCheck'@ should only be used when you are sure the meta will be type-checked (in a term judgement)
      later on.
  -}
newMetaTermNoCheck :: (DeBruijnLevel v, MonadScoper sys sc) =>
    -- -> Degree sys v {-^ Degree up to which it should be solved -}
    Ctx Type sys v ->
    MetaNeutrality ->
    Maybe (Algorithm sys v) ->
    String ->
    sc (Term sys v)
newMetaTermNoCheck gamma neutrality maybeAlg reason = do
  (meta, depcies) <- newMetaID gamma reason
  return $ Expr2 $ TermMeta neutrality meta (Compose depcies) (Compose maybeAlg)
  
newMetaTypeNoCheck :: (DeBruijnLevel v, MonadScoper sys sc) =>
    -- -> Degree sys v {-^ Degree up to which it should be solved -}
    Ctx Type sys v ->
    String ->
    sc (Type sys v)
newMetaTypeNoCheck gamma reason =
  Type <$> newMetaTermNoCheck gamma MetaBlocked Nothing reason

instance (MonadScoper sys sc, MonadTrans mT, MonadFail (mT sc)) => MonadScoper sys (mT sc) where
  newMetaID gamma reason =
    lift $ newMetaID gamma reason
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
  awaitMeta :: forall t v . Solvable sys t => String -> Int -> [(Mode sys :*: Term sys) v] -> whn (Maybe (t v))

instance (MonadWHN sys whn, MonadTrans mT, MonadFail (mT whn)) => MonadWHN sys (mT whn) where
  awaitMeta reason meta depcies = lift $ awaitMeta reason meta depcies

class (
    Degrees sys,
    MonadWHN sys tc
  ) => MonadTC sys tc | tc -> sys where
  withParent :: forall a . Constraint sys -> tc a -> tc a
  useMaybeParent :: tc (Maybe (Constraint sys))
  --term4newImplicit :: Ctx ty sys v Void -> tc (Term sys v)
  --mode4newImplicit :: Ctx ty sys v Void -> tc (mode v)
  --modty4newImplicit :: Ctx ty sys v Void -> tc (modty v)
  --genVarName :: tc Raw.Name
  --newConstraintID :: tc Int
  {-| Create and register a new constraint. -}
  defConstraint ::
    Judgement sys ->
    String ->
    tc (Constraint sys)
  {-| Add a check for this constraint to the task stack. -}
  addConstraint :: Constraint sys -> tc ()
  addNewConstraint ::
    Judgement sys ->
    String ->
    tc ()
  {-| For instances. Will only be considered if all nice constraints have been considered. -}
  addConstraintReluctantly :: Constraint sys -> tc ()
  {-| Provide a solution for the meta. All continuations thus unblocked are added to the task stack.
      Return @'Nothing'@ if you don't want to solve the meta.
      The returned result of type 'a' is just passed back to the caller.
  -}
  solveMeta ::
    (Solvable sys t) =>
    Int ->
    (forall v .
      (Eq v, DeBruijnLevel v) =>
      Ctx Type sys v ->
      tc (Maybe (t v), a)
    ) -> tc a
  --{-| Returns the value of the meta, if existent. Awakens the scoper-induced meta if still asleep.
  ---}
  --getMeta :: Int -> [Term sys v] -> tc (Maybe (Term sys v))
  --{-| Shove a judgement aside; it will only be reconsidered when one of the given metas has been solved. -}
  --blockOnMetas :: [Int] -> Constraint sys -> tc ()
  {-| Aborts (rather than cancels) computation.
      For every call to @'awaitMeta'@ that didn't yield a result, the continuation as of that point
      is saved. The first time one of the corresponding metas is resolved, the continuation from that point will be run. -}
  tcBlock :: String -> tc a
  tcUnblock :: WorryID -> tc ()
  tcReport :: String -> tc ()
  tcFail :: String -> tc a
  --leqMod :: Modality sys v -> Modality sys v -> tc Bool
  -- | DO NOT USE @'awaitMeta'@ WITHIN!
  --selfcontained :: Constraint sys -> tc () -> tc ()

await :: (MonadWHN sys whn, SysAnalyzer sys) =>
  String -> Term sys v -> whn (Maybe (Term sys v))
await reason (Expr2 (TermMeta flagEta meta (Compose depcies) alg)) = runMaybeT $ do
  term <- MaybeT $ awaitMeta reason meta depcies
  MaybeT $ await reason term
await reason t = return $ Just t

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
newMetaTerm :: (MonadTC sys tc, DeBruijnLevel v, SysAnalyzer sys) =>
  Ctx Type sys v ->
  Type sys v ->
  MetaNeutrality ->
  String ->
  tc (Term sys v)
newMetaTerm gamma ty neutrality reason = do
  t <- newMetaTermNoCheck gamma neutrality Nothing reason
  addNewConstraint
    (JudTerm gamma t ty)
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
newMetaType :: (MonadTC sys tc, DeBruijnLevel v, SysAnalyzer sys) =>
  Ctx Type sys v ->
  String ->
  tc (Type sys v)
newMetaType gamma reason = do
  t <- Type <$> newMetaTermNoCheck gamma MetaBlocked Nothing reason
  addNewConstraint
    (JudType gamma t)
    reason
  return t

-- | Not to be used by the Scoper.
-- | No eta flag is given: it is set to @False@, as there is no eta-equality in the universe.
-- | No algorithm is given: this isn't used by the scoper anyway.
newMetaTypeRel :: (MonadTC sys tc, DeBruijnLevel v, SysAnalyzer sys) =>
  ModedDegree sys v ->
  Ctx (Twice2 Type) sys v ->
  Type sys v ->
  String ->
  tc (Type sys v)
newMetaTypeRel ddeg gamma ty2 reason = do
  ty1 <- Type <$> newMetaTermNoCheck (fstCtx gamma) MetaBlocked Nothing reason
  addNewConstraint
    (JudTypeRel ddeg gamma (Twice2 ty1 ty2))
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
