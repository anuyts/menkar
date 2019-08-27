{-# LANGUAGE AllowAmbiguousTypes, UndecidableInstances #-}

module Menkar.Basic.Context.DeBruijnLevel where

import Prelude hiding (take, length)

import Control.DeepSeq.Redone
import Data.Constraint.AlgebraicFunctor

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

class (NFData v, Coercible Int v) => DeBruijnLevel v where
  eqVar :: v -> v -> Bool
  eqVar = coerce ((==) :: Int -> Int -> Bool)
  
  size :: Int
  
  getDeBruijnLevel :: v -> Int
  getDeBruijnLevel v = size @v - 1 - getDeBruijnIndex v
  --getDeBruijnLevel v = fromIntegral $ fromMaybe unreachable $ elemIndex v $ listAll @v
  
  forDeBruijnLevel :: Int -> v
  forDeBruijnLevel n = forDeBruijnIndex @v (size @v - 1 - n)
  --forDeBruijnLevel n = ((Just <$> listAll @v) ++ repeat Nothing) `genericIndex` n
  
  getDeBruijnIndex :: v -> Int
  getDeBruijnIndex = coerce
  
  {-forDeBruijnIndex :: Int -> Maybe v
  forDeBruijnIndex = lowerCoyoneda . forDeBruijnIndexCoyoneda
  forDeBruijnIndexCoyoneda :: Int -> Coyoneda Maybe v
  forDeBruijnIndexCoyoneda n = liftCoyoneda $! forDeBruijnLevel @v (size @v - 1 - n)-}
  forDeBruijnIndex :: Int -> v
  forDeBruijnIndex = coerce

  forallVars :: forall a . (v -> a) -> [a]
  forallVars f = f <$> listAll

  forallVarsRev :: forall a . (v -> a) -> [a]
  forallVarsRev f = f <$> listAllRev

  -- | list in order of appearing, i.e. by DB LEVEL.
  listAll :: [v]
  listAll = forDeBruijnIndex !<$> (take sz $ [sz - 1, sz - 2..])
    where sz = size @v
  
  listAllRev :: [v]
  listAllRev = forDeBruijnIndex !<$> (take (size @v) $ [0..])

  atVarRev :: forall a . v -> [a] -> a
  atVarRev v as = as !! getDeBruijnLevel v
  
  {-# MINIMAL size #-}

----------------------------------

--instance (NFData1 DeBruijnLevel f, DeBruijnLevel v) => NFData (f v) where
--  rnf = rnf1 @DeBruijnLevel

newtype EqVar v = EqVar {getEqVar :: v}
instance DeBruijnLevel v => Eq (EqVar v) where
  EqVar v1 == EqVar v2 = eqVar v1 v2

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

----------------------------------

class (AlgebraicFunctor DeBruijnLevel f) => DBFunctor f where
  rename :: (DeBruijnLevel v, DeBruijnLevel w) => (v -> w) -> f v -> f w
  rename = algmap @DeBruijnLevel

(<#>) :: (DBFunctor f, DeBruijnLevel v, DeBruijnLevel w) => (v -> w) -> f v -> f w
(<#>) = rename

renameCoe :: (DeBruijnLevel v, DeBruijnLevel w) => (v -> w) -> f v -> f w
renameCoe f = unsafeCoerce
(!<#>) :: (DeBruijnLevel v, DeBruijnLevel w) => (v -> w) -> f v -> f w
(!<#>) = renameCoe
  
instance (AlgebraicFunctor DeBruijnLevel f) => DBFunctor f where
  
----------------------------------
  
class DBPointed f where
  dbpure :: (DeBruijnLevel v) => v -> f v

class (forall x . DeBruijnLevel x => DeBruijnLevel (t x)) => DBMonoTraversable t where
  dbmonoTraverse :: forall f v w .
    (DeBruijnLevel v, DeBruijnLevel w, DBPointed f, DBFunctor f) =>
    (v -> f w) -> t v -> f (t w)
  
----------------------------------

data DBCoyoneda f x = forall y . (DeBruijnLevel x, DeBruijnLevel y) => DBCoyoneda (y -> x) (f y)

instance (DBFunctor f) => AlgebraicFunctor DeBruijnLevel (DBCoyoneda f) where
  algmap f (DBCoyoneda q fx) = DBCoyoneda (f . q) fx

liftDBCoyoneda :: (DeBruijnLevel v) => f v -> DBCoyoneda f v
liftDBCoyoneda = DBCoyoneda id

lowerDBCoyoneda :: (DeBruijnLevel v, DBFunctor f) => DBCoyoneda f v -> f v
lowerDBCoyoneda (DBCoyoneda q fv) = q <#> fv

hoistDBCoyoneda ::
  (forall x . DeBruijnLevel x => f x -> g x) ->
  (DeBruijnLevel a => DBCoyoneda f a -> DBCoyoneda g a)
hoistDBCoyoneda f (DBCoyoneda q fv) = DBCoyoneda q (f fv)
