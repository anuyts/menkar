{-# LANGUAGE GeneralizedNewtypeDeriving, NoDeriveAnyClass #-}

module Menkar.Basic.Context.Variable where

import Data.Bifunctor
import Control.Exception.AssertFalse
import Data.Void
import Data.Number.Nat
import Data.Proxy

--data VarWkn v = VarLast | VarWkn v deriving (Show, Functor, Foldable, Traversable)
newtype VarExt v = VarExt {runVarWkn :: Maybe v}
  deriving (Show, Functor, Foldable, Traversable, Eq)
pattern VarWkn v = VarExt (Just v)
pattern VarLast = VarExt (Nothing)
{- # COMPLETE VarWkn, VarLast #-}

newtype VarLeftExt v = VarLeftExt {runVarLeftExt :: Maybe v}
  deriving (Show, Functor, Foldable, Traversable, Eq)
pattern VarLeftWkn v = VarLeftExt (Just v)
pattern VarFirst = VarLeftExt (Nothing)
{- # COMPLETE VarLeftWkn, VarFirst #-}

newtype VarOpenCtx v w = VarOpenCtx {runVarOpenCtx :: Either v w}
  deriving (Show, Functor, Foldable, Traversable, Bifunctor, Eq)
pattern VarFromCtx v = VarOpenCtx (Left v)
pattern VarBeforeCtx w = VarOpenCtx (Right w)
{- # COMPLETE VarFromCtx, VarBeforeCtx #-}
unVarFromCtx :: VarOpenCtx v Void -> v
unVarFromCtx (VarFromCtx v) = v
unVarFromCtx (VarBeforeCtx w) = absurd w
unVarFromCtx _ = unreachable

varLeftEat :: VarOpenCtx v (VarExt w) -> VarOpenCtx (VarLeftExt v) w
varLeftEat (VarBeforeCtx (VarWkn w)) = VarBeforeCtx w
varLeftEat (VarBeforeCtx VarLast) = VarFromCtx $ VarFirst
varLeftEat (VarFromCtx v) = VarFromCtx $ VarLeftWkn v
varLeftEat _ = unreachable

--newtype VarDiv v = VarDiv {runVarDiv :: v} deriving (Show, Functor, Foldable, Traversable)

newtype VarInModule v = VarInModule {runVarInModule :: v}
  deriving (Show, Functor, Foldable, Traversable, Eq)

-------------------------------------------------

class DeBruijnLevel v where
  size :: Proxy v -> Nat
  getDeBruijnLevel :: Proxy v -> v -> Nat
  forDeBruijnLevel :: Proxy v -> Nat -> Maybe v

instance DeBruijnLevel Void where
  size p = 0
  getDeBruijnLevel p = absurd
  forDeBruijnLevel p n = Nothing

proxyUnVarWkn :: Proxy (VarExt v) -> Proxy v
proxyUnVarWkn Proxy = Proxy
instance DeBruijnLevel v => DeBruijnLevel (VarExt v) where
  size p = size (proxyUnVarWkn p) + 1
  getDeBruijnLevel p (VarWkn v) = getDeBruijnLevel Proxy v
  getDeBruijnLevel p VarLast = size p - 1
  getDeBruijnLevel p _ = unreachable
  forDeBruijnLevel p n
    | n == size p - 1 = Just VarLast
    | otherwise = VarWkn <$> forDeBruijnLevel Proxy n

proxyUnVarLeftWkn :: Proxy (VarLeftExt v) -> Proxy v
proxyUnVarLeftWkn Proxy = Proxy
instance DeBruijnLevel v => DeBruijnLevel (VarLeftExt v) where
  size p = size (proxyUnVarLeftWkn p) + 1
  getDeBruijnLevel p (VarLeftWkn v) = getDeBruijnLevel Proxy v
  getDeBruijnLevel p VarFirst = size p - 1
  getDeBruijnLevel p _ = unreachable
  forDeBruijnLevel p n
    | n == size p - 1 = Just VarFirst
    | otherwise = VarLeftWkn <$> forDeBruijnLevel Proxy n

instance DeBruijnLevel v => DeBruijnLevel (VarInModule v) where
  size p = size $ runVarInModule <$> p
  getDeBruijnLevel p (VarInModule v) = getDeBruijnLevel Proxy v
  forDeBruijnLevel p n = VarInModule <$> forDeBruijnLevel Proxy n
