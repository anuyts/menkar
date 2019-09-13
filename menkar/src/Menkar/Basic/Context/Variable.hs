module Menkar.Basic.Context.Variable where

import Control.Exception.AssertFalse
import Control.DeepSeq.Redone

import Data.Bifunctor
import Data.Void
import GHC.Generics
import GHC.Stack
import Data.Functor.Classes
import Data.Coerce

data VarExt v = VarWkn !v | VarLast
  deriving (Show, Functor, Foldable, Traversable, Eq, Generic1, NFData1)
instance Eq1 VarExt where
  liftEq eq (VarWkn v1) (VarWkn v2) = eq v1 v2
  liftEq eq VarLast VarLast = True
  liftEq eq _ _ = False

data VarLeftExt v = VarFirst | VarLeftWkn !v
  deriving (Show, Functor, Foldable, Traversable, Eq, Generic1, NFData1)
instance Eq1 VarLeftExt where
  liftEq eq (VarLeftWkn v1) (VarLeftWkn v2) = eq v1 v2
  liftEq eq VarFirst VarFirst = True
  liftEq eq _ _ = False

--newtype VarDiv v = VarDiv {runVarDiv :: v} deriving (Show, Functor, Foldable, Traversable)

newtype VarInModule v = VarInModule {runVarInModule :: v}
  deriving (Show, Functor, Foldable, Traversable, Eq, Generic1)
  deriving anyclass NFData1
instance Eq1 VarInModule where
  liftEq = coerce
