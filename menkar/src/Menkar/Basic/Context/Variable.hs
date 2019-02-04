module Menkar.Basic.Context.Variable where

import Control.Exception.AssertFalse

import Data.Bifunctor
import Data.Void
import Data.Number.Nat

import GHC.Stack

data VarExt v = VarWkn v | VarLast
  deriving (Show, Functor, Foldable, Traversable, Eq)

data VarLeftExt v = VarFirst | VarLeftWkn v
  deriving (Show, Functor, Foldable, Traversable, Eq)

data VarOpenCtx v w = VarFromCtx v | VarBeforeCtx w
  deriving (Show, Functor, Foldable, Traversable, Eq)
instance Bifunctor VarOpenCtx where
  bimap f g (VarFromCtx v) = VarFromCtx (f v)
  bimap f g (VarBeforeCtx w) = VarBeforeCtx (g w)
unVarFromCtx :: VarOpenCtx v Void -> v
unVarFromCtx (VarFromCtx v) = v
unVarFromCtx (VarBeforeCtx w) = absurd w
unVarBeforeCtxUnsafe :: HasCallStack => VarOpenCtx v w -> w
unVarBeforeCtxUnsafe (VarFromCtx v) = unreachable
unVarBeforeCtxUnsafe (VarBeforeCtx w) = w
externalizeVar :: VarOpenCtx v Void -> VarOpenCtx u v
externalizeVar (VarFromCtx v) = VarBeforeCtx v
externalizeVar (VarBeforeCtx w) = absurd w

varLeftEat :: VarOpenCtx v (VarExt w) -> VarOpenCtx (VarLeftExt v) w
varLeftEat (VarBeforeCtx (VarWkn w)) = VarBeforeCtx w
varLeftEat (VarBeforeCtx VarLast) = VarFromCtx $ VarFirst
varLeftEat (VarFromCtx v) = VarFromCtx $ VarLeftWkn v

--newtype VarDiv v = VarDiv {runVarDiv :: v} deriving (Show, Functor, Foldable, Traversable)

newtype VarInModule v = VarInModule {runVarInModule :: v}
  deriving (Show, Functor, Foldable, Traversable, Eq)
