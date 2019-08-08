module Menkar.Basic.Context.DeBruijnLevel where

import Prelude hiding (take, length)

import Menkar.Basic.Context.Variable

import Data.Bifunctor
import Control.Exception.AssertFalse
import Data.Void
import Data.Proxy
import Data.Maybe
import Data.List
import Data.Functor.Compose
import Data.Functor.Identity
import Unsafe.Coerce

-------------------------------------------------

class Eq v => DeBruijnLevel v where
  size :: Proxy v -> Int
  size p = length $ listAll p
  getDeBruijnLevel :: Proxy v -> v -> Int
  getDeBruijnLevel p v = fromIntegral $ fromMaybe unreachable $ elemIndex v $ listAll p
  forDeBruijnLevel :: Proxy v -> Int -> Maybe v
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
  forDeBruijnLevel p n
    | n == size p - 1 = Just VarLast
    | otherwise = VarWkn <$> forDeBruijnLevel Proxy n

proxyUnVarLeftWkn :: Proxy (VarLeftExt v) -> Proxy v
proxyUnVarLeftWkn Proxy = Proxy
instance DeBruijnLevel v => DeBruijnLevel (VarLeftExt v) where
  size p = size (proxyUnVarLeftWkn p) + 1
  getDeBruijnLevel p (VarLeftWkn v) = getDeBruijnLevel Proxy v
  getDeBruijnLevel p VarFirst = size p - 1
  forDeBruijnLevel p n
    | n == size p - 1 = Just VarFirst
    | otherwise = VarLeftWkn <$> forDeBruijnLevel Proxy n

instance DeBruijnLevel v => DeBruijnLevel (VarInModule v) where
  size p = size $ runVarInModule <$> p
  getDeBruijnLevel p (VarInModule v) = getDeBruijnLevel Proxy v
  forDeBruijnLevel p n = VarInModule <$> forDeBruijnLevel Proxy n

deriving instance Eq (f (g v)) => Eq (Compose f g v)
instance DeBruijnLevel (f (g v)) => DeBruijnLevel (Compose f g v) where
  size p = size (Proxy :: Proxy (f (g v)))
  getDeBruijnLevel p (Compose v) = getDeBruijnLevel Proxy v
  forDeBruijnLevel p n = Compose <$> forDeBruijnLevel Proxy n
  listAll p = Compose <$> listAll Proxy

instance DeBruijnLevel v => DeBruijnLevel (Identity v) where
  size p = size (Proxy :: Proxy v)
  getDeBruijnLevel p (Identity v) = getDeBruijnLevel Proxy v
  forDeBruijnLevel p n = Identity <$> forDeBruijnLevel Proxy n
  listAll p = Identity <$> listAll Proxy

----------------------------------

data ForSomeDeBruijnLevel a = forall v . DeBruijnLevel v => ForSomeDeBruijnLevel (a v)
forThisDeBruijnLevel :: (forall v . DeBruijnLevel v => a v -> t) -> ForSomeDeBruijnLevel a -> t
forThisDeBruijnLevel f (ForSomeDeBruijnLevel a) = f a
mapDeBruijnLevel :: (forall v . DeBruijnLevel v => a v -> b v) -> ForSomeDeBruijnLevel a -> ForSomeDeBruijnLevel b
mapDeBruijnLevel f (ForSomeDeBruijnLevel a) = ForSomeDeBruijnLevel $ f a
atThisDeBruijnLevel :: forall f a b . (Functor f) =>
  (forall v . DeBruijnLevel v => a v -> f (b v)) -> ForSomeDeBruijnLevel a -> f (ForSomeDeBruijnLevel b)
atThisDeBruijnLevel g (ForSomeDeBruijnLevel a) = ForSomeDeBruijnLevel <$> g a
unsafeForceDeBruijnLevel :: forall v a . (Functor a, DeBruijnLevel v) => ForSomeDeBruijnLevel a -> a v
unsafeForceDeBruijnLevel (ForSomeDeBruijnLevel a) = unsafeCoerce <$> a
