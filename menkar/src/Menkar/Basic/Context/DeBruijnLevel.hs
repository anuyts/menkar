{-# LANGUAGE AllowAmbiguousTypes, UndecidableInstances #-}

module Menkar.Basic.Context.DeBruijnLevel where

import Prelude hiding (take, length)

import Menkar.Basic.Context.Variable

import Control.DeepSeq.Redone

import Data.Bifunctor
import Control.Exception.AssertFalse
import Data.Void
import Data.Maybe
import Data.List
import Data.Functor.Compose
import Data.Functor.Identity
import Data.Functor.Coerce
import Data.Functor.Classes
import Unsafe.Coerce
import Data.Coerce
--import Data.Functor.Coyoneda

-------------------------------------------------

class (NFData v) => DeBruijnLevel v where
  eqVar :: v -> v -> Bool
  
  size :: Int
  
  getDeBruijnLevel :: v -> Int
  getDeBruijnLevel v = size @v - 1 - getDeBruijnIndex v
  --getDeBruijnLevel v = fromIntegral $ fromMaybe unreachable $ elemIndex v $ listAll @v
  
  forDeBruijnLevel :: Int -> v
  forDeBruijnLevel n = forDeBruijnIndex @v (size @v - 1 - n)
  --forDeBruijnLevel n = ((Just <$> listAll @v) ++ repeat Nothing) `genericIndex` n
  
  getDeBruijnIndex :: v -> Int
  getDeBruijnIndex v = size @v - 1 - getDeBruijnLevel v
  
  {-forDeBruijnIndex :: Int -> Maybe v
  forDeBruijnIndex = lowerCoyoneda . forDeBruijnIndexCoyoneda
  forDeBruijnIndexCoyoneda :: Int -> Coyoneda Maybe v
  forDeBruijnIndexCoyoneda n = liftCoyoneda $! forDeBruijnLevel @v (size @v - 1 - n)-}
  forDeBruijnIndex :: Int -> v
  forDeBruijnIndex n = forDeBruijnLevel @v (size @v - 1 - n)

  forallVars :: forall a . (v -> a) -> [a]
  forallVars f = reverse $ forallVarsRev f

  forallVarsRev :: forall a . (v -> a) -> [a]
  forallVarsRev f = reverse $ forallVars f
  
  listAll :: [v]
  listAll = forallVars id
  
  listAllRev :: [v]
  listAllRev = forallVarsRev id

  atVarRev :: forall a . v -> [a] -> a
  atVarRev v as = as !! getDeBruijnLevel v
  
  {-# MINIMAL eqVar, size,
      (getDeBruijnIndex | getDeBruijnLevel),
      (forDeBruijnIndex | forDeBruijnLevel),
      (forallVars | forallVarsRev) #-}

--instance (NFData1 DeBruijnLevel f, DeBruijnLevel v) => NFData (f v) where
--  rnf = rnf1 @DeBruijnLevel

newtype EqVar v = EqVar {getEqVar :: v}
instance DeBruijnLevel v => Eq (EqVar v) where
  EqVar v1 == EqVar v2 = eqVar v1 v2

--------------------------------------

instance DeBruijnLevel Void where
  eqVar = absurd
  size = 0
  getDeBruijnLevel = absurd
  forDeBruijnLevel n = unreachable
  getDeBruijnIndex = absurd
  forDeBruijnIndex n = unreachable
  forallVars f = []
  forallVarsRev f = []
  atVarRev = absurd

instance DeBruijnLevel v => DeBruijnLevel (VarExt v) where
  eqVar = liftEq eqVar
  size = size @v + 1
  getDeBruijnLevel (VarWkn v) = getDeBruijnLevel v
  getDeBruijnLevel VarLast = size @v
  forDeBruijnIndex n
    | n == 0 = VarLast
    | otherwise = VarWkn $! forDeBruijnIndex (n - 1)
  forallVarsRev f = f VarLast : (forallVarsRev $ f . VarWkn)
  atVarRev v [] = unreachable
  atVarRev VarLast (a : as) = a
  atVarRev (VarWkn v) (a : as) = atVarRev v as

{-
proxyUnVarLeftWkn :: Proxy (VarLeftExt v) -> Proxy v
proxyUnVarLeftWkn Proxy = Proxy
instance DeBruijnLevel v => DeBruijnLevel (VarLeftExt v) where
  size p = size (proxyUnVarLeftWkn p) + 1
  getDeBruijnLevel p (VarLeftWkn v) = getDeBruijnLevel Proxy v
  getDeBruijnLevel p VarFirst = size p - 1
  forDeBruijnLevel p n
    | n == size p - 1 = Just VarFirst
    | otherwise = VarLeftWkn <$> forDeBruijnLevel Proxy n
-}

instance DeBruijnLevel v => DeBruijnLevel (VarInModule v) where
  eqVar = liftEq eqVar
  size = size @v
  getDeBruijnLevel (VarInModule v) = getDeBruijnLevel v
  getDeBruijnIndex (VarInModule v) = getDeBruijnIndex v
  forDeBruijnLevel n = VarInModule $ forDeBruijnLevel n
  forDeBruijnIndex n = VarInModule $ forDeBruijnIndex n
  forallVars f = forallVars $ f . VarInModule
  forallVarsRev f = forallVarsRev $ f . VarInModule
  atVarRev (VarInModule v) = atVarRev v

--deriving instance Eq (f (g v)) => Eq (Compose f g v)
instance (DeBruijnLevel (f (g v)),
          NFData (f (g v))) => DeBruijnLevel (Compose f g v) where
  eqVar (Compose fgv1) (Compose fgv2) = eqVar fgv1 fgv2
  size = size @(f (g v))
  getDeBruijnLevel (Compose v) = getDeBruijnLevel v
  getDeBruijnIndex (Compose v) = getDeBruijnIndex v
  forDeBruijnLevel n = Compose $ forDeBruijnLevel n
  forDeBruijnIndex n = Compose $ forDeBruijnIndex n
  forallVars f = forallVars $ f . Compose
  forallVarsRev f = forallVarsRev $ f . Compose
  atVarRev (Compose v) = atVarRev v

instance DeBruijnLevel v => DeBruijnLevel (Identity v) where
  eqVar (Identity v1) (Identity v2) = eqVar v1 v2
  size = size @v
  getDeBruijnLevel (Identity v) = getDeBruijnLevel v
  getDeBruijnIndex (Identity v) = getDeBruijnIndex v
  forDeBruijnLevel n = Identity $ forDeBruijnLevel n
  forDeBruijnIndex n = Identity $ forDeBruijnIndex n
  forallVars f = forallVars $ f . Identity
  forallVarsRev f = forallVarsRev $ f . Identity
  atVarRev (Identity v) = atVarRev v

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
