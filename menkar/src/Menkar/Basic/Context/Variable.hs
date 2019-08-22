module Menkar.Basic.Context.Variable where

import Control.Exception.AssertFalse
import Control.DeepSeq.Picky

import Data.Bifunctor
import Data.Void
import GHC.Generics

import GHC.Stack

data VarExt v = VarWkn v | VarLast
  deriving (Show, Functor, Foldable, Traversable, Eq, Generic1, NFData1)

data VarLeftExt v = VarFirst | VarLeftWkn v
  deriving (Show, Functor, Foldable, Traversable, Eq, Generic1, NFData1)

--newtype VarDiv v = VarDiv {runVarDiv :: v} deriving (Show, Functor, Foldable, Traversable)

newtype VarInModule v = VarInModule {runVarInModule :: v}
  deriving (Show, Functor, Foldable, Traversable, Eq, Generic1, NFData1)
