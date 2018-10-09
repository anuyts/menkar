{-# LANGUAGE GeneralizedNewtypeDeriving, NoDeriveAnyClass #-}

module Menkar.Fine.Context.Variable where

import Data.Bifunctor
import Control.Exception.AssertFalse
import Data.Void

--data VarWkn v = VarLast | VarWkn v deriving (Show, Functor, Foldable, Traversable)
newtype VarExt v = VarExt {runVarWkn :: Maybe v} deriving (Show, Functor, Foldable, Traversable)
pattern VarWkn v = VarExt (Just v)
pattern VarLast = VarExt (Nothing)
{- # COMPLETE VarWkn, VarLast #-}

newtype VarLeftExt v = VarLeftExt {runVarLeftExt :: Maybe v} deriving (Show, Functor, Foldable, Traversable)
pattern VarLeftWkn v = VarLeftExt (Just v)
pattern VarFirst = VarLeftExt (Nothing)
{- # COMPLETE VarLeftWkn, VarFirst #-}

newtype VarOpenCtx v w = VarOpenCtx {runVarOpenCtx :: Either v w} deriving (Show, Functor, Foldable, Traversable, Bifunctor)
pattern VarFromCtx v = VarOpenCtx (Left v)
pattern VarBeforeCtx w = VarOpenCtx (Right w)
{- # COMPLETE VarFromCtx, VarBeforeCtx #-}
unVarFromCtx :: VarOpenCtx v Void -> v
unVarFromCtx (VarFromCtx v) = v
unVarFromCtx (VarBeforeCtx w) = absurd w
unVarFromCtx _ = unreachable

newtype VarDiv v = VarDiv {runVarDiv :: v} deriving (Show, Functor, Foldable, Traversable)

newtype VarInModule v = VarInModule {runVarInModule :: v} deriving (Show, Functor, Foldable, Traversable)
