module Menkar.Basic.Context.DeBruijnLevel where

import Prelude hiding (take, length)

import Data.Bifunctor
import Control.Exception.AssertFalse
import Data.Void
import Data.Number.Nat
import Data.Proxy
import Data.Maybe
import Data.List hiding (take, length)

import Menkar.Basic.Context.Variable

-------------------------------------------------

class Eq v => DeBruijnLevel v where
  size :: Proxy v -> Nat
  size p = length $ listAll p
  getDeBruijnLevel :: Proxy v -> v -> Nat
  getDeBruijnLevel p v = fromIntegral $ fromMaybe unreachable $ elemIndex v $ listAll p
  forDeBruijnLevel :: Proxy v -> Nat -> Maybe v
  forDeBruijnLevel p n = ((Just <$> listAll p) ++ repeat Nothing) `genericIndex` n
  listAll :: Proxy v -> [v]
  listAll p = fromMaybe unreachable . forDeBruijnLevel p <$> take (size p) [0..]
  {-# MINIMAL size, getDeBruijnLevel, forDeBruijnLevel | listAll #-}

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


