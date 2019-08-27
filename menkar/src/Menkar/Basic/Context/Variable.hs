{-# LANGUAGE UndecidableInstances #-}

module Menkar.Basic.Context.Variable where

import Menkar.Basic.Context.DeBruijnLevel

import Control.Exception.AssertFalse
import Control.DeepSeq.Redone
import Data.Constraint.AlgebraicFunctor
import Data.Functor.Coerce

import Data.Bifunctor
import Data.Void
import GHC.Generics
import GHC.Stack
import Data.Functor.Classes
import Data.Coerce
import Data.Functor.Identity
import Data.Functor.Compose

--------------------------------

newtype VarClosed = VarClosedDBI Int
  deriving (Show, Generic, NFData)

absurdVar :: forall a . VarClosed -> a
absurdVar v = unreachable

instance DeBruijnLevel VarClosed where
  size = 0

--------------------------------

newtype VarExt v = VarExtDBI Int
  deriving (Show, Generic1, NFData1)

getVarWkn :: DeBruijnLevel v => VarExt v -> Maybe v
getVarWkn (VarExtDBI 0) = Nothing
getVarWkn (VarExtDBI i) = Just $! coerce i

pattern VarLast :: VarExt v
pattern VarLast = VarExtDBI 0
pattern VarWkn :: DeBruijnLevel v => () => v -> VarExt v
pattern VarWkn v <- (getVarWkn -> Just v)
  where VarWkn v = VarExtDBI $ coerce v + 1
{-# COMPLETE VarLast, VarWkn #-}

instance (DeBruijnLevel v) => DeBruijnLevel (VarExt v) where
  size = size @v + 1
  
instance (forall v . c v => DeBruijnLevel v) => (AlgebraicFunctor c VarExt) where
  algmap f VarLast = VarLast
  algmap f (VarWkn v) = VarWkn $ f v

instance DBMonoTraversable VarExt where
  dbmonoTraverse h VarLast = dbpure $ VarLast
  dbmonoTraverse h (VarWkn v) = VarWkn <#> h v

--------------------------------

newtype VarInModule v = VarInModule {runVarInModule :: v}
  deriving (Show, Functor, Foldable, Traversable, Eq, Generic1, NFData1)

deriving instance (AlgebraicFunctor c VarInModule)

instance (DeBruijnLevel v) => DeBruijnLevel (VarInModule v) where
  size = size @v
  
instance DBMonoTraversable VarInModule where
  dbmonoTraverse h (VarInModule v) = VarInModule !<#> h v

--------------------------------

instance (DeBruijnLevel (g (f v))) => DeBruijnLevel (Compose g f v) where
  size = size @(g (f v))

composeAlgMapTest :: forall v w .
  (DeBruijnLevel v, DeBruijnLevel w) =>
  (v -> w) ->
  Compose VarExt VarExt v ->
  Compose VarExt VarExt w
composeAlgMapTest f ceev = algmap @DeBruijnLevel f ceev

instance (DBMonoTraversable g, DBMonoTraversable f) => DBMonoTraversable (Compose g f) where
  dbmonoTraverse h (Compose gfv) = Compose !<#> (dbmonoTraverse $ dbmonoTraverse h) gfv

--------------------------------

instance (DeBruijnLevel v) => DeBruijnLevel (Identity v) where
  size = size @v
deriving instance (AlgebraicFunctor DeBruijnLevel Identity)
  
instance DBMonoTraversable Identity where
  dbmonoTraverse h (Identity v) = Identity !<#> h v
