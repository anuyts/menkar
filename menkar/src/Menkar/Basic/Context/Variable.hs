module Menkar.Basic.Context.Variable where

import Control.Exception.AssertFalse

import Data.Bifunctor
import Data.Void

import GHC.Stack

data VarExt v = VarWkn v | VarLast
  deriving (Show, Functor, Foldable, Traversable, Eq)

data VarLeftExt v = VarFirst | VarLeftWkn v
  deriving (Show, Functor, Foldable, Traversable, Eq)

-- | Obsolete.
unVarFromCtx :: v -> v
unVarFromCtx v = v

-- | Obsolete.
pattern VarFromCtx v = v

--newtype VarDiv v = VarDiv {runVarDiv :: v} deriving (Show, Functor, Foldable, Traversable)

newtype VarInModule v = VarInModule {runVarInModule :: v}
  deriving (Show, Functor, Foldable, Traversable, Eq)
