{-# LANGUAGE UndecidableInstances, AllowAmbiguousTypes #-}

{-| Implementation of NFData using QuantifiedConstraints. -}

module Control.DeepSeq.Picky where

import Data.Functor.Functor1
import Data.Constraint.And
import Data.Constraint.Preimage

import GHC.Generics
import Data.Constraint.Trivial
import Data.Constraint.Witness
import Data.Functor.Compose
import Data.Kind
import Data.Void
import Data.Functor.Identity

import qualified Control.DeepSeq as DS

type family GoodArg (f :: * -> *) :: * -> Constraint

class NFData1 (f :: * -> *) where
  rnf1 :: forall x . GoodArg f x => f x -> ()
  default rnf1 ::
    forall x . (GoodArg (Rep1 f) x, Generic1 f, NFData1 (Rep1 f)) => f x -> ()
  rnf1 = rnf1 . from1

class NFData (a :: *) where
  rnf :: a -> ()
  default rnf :: (Generic a, NFData1 (Rep a), GoodArg (Rep a) ()) => a -> ()
  rnf = rnf1 @_ @() . from

instance (NFData1 f, GoodArg f x) => NFData (f x) where
  rnf = rnf1

rwhnf :: a -> ()
rwhnf = DS.rwhnf

-----------------

type instance GoodArg V1 = Unconstrained
instance NFData1 V1 where
  rnf1 x = case x of {}

type instance GoodArg U1 = Unconstrained
instance NFData1 U1 where
  rnf1 U1 = ()

type instance GoodArg Par1 = NFData
instance NFData1 Par1 where
  rnf1 (Par1 x) = rnf x

type instance GoodArg (Rec1 f) = GoodArg f
instance (NFData1 f) => NFData1 (Rec1 f) where
  rnf1 (Rec1 fx) = rnf1 fx

type instance GoodArg (K1 i a) = Unconstrained
instance (NFData a) => NFData1 (K1 i a) where
  rnf1 (K1 a) = rnf a

type instance GoodArg (M1 i c f) = GoodArg f
instance (NFData1 f) => NFData1 (M1 i c f) where
  rnf1 (M1 fx) = rnf1 fx

type instance GoodArg (f :+: g) = GoodArg f :&: GoodArg g
instance (NFData1 f, NFData1 g) => NFData1 (f :+: g) where
  rnf1 (L1 fx) = rnf1 fx
  rnf1 (R1 gx) = rnf1 gx

type instance GoodArg (f :*: g) = GoodArg f :&: GoodArg g
instance (NFData1 f, NFData1 g) => NFData1 (f :*: g) where
  rnf1 (fx :*: gx) = rnf1 fx `seq` rnf1 gx

{- from1 uses @Functor f@, I don't trust it!
instance (NFData1 g) => NFData1 (g :.: f) where
type instance GoodArg (g :.: f) = After f (GoodArg g)
  rnf1 (Comp1 gfx) = rnf1 gfx -}

type instance GoodArg (Compose g f) = After f (GoodArg g)
instance (NFData1 g) => NFData1 (Compose g f) where
  rnf1 (Compose gfx) = rnf1 gfx

---------------------------------

instance NFData Char where rnf = rwhnf

deriving instance NFData Void

---------------------------------

type instance GoodArg Identity = NFData
instance NFData1 Identity where
  rnf1 (Identity x) = rnf x

type instance GoodArg Maybe = NFData
deriving instance NFData1 Maybe

type instance GoodArg [] = NFData
instance NFData1 [] where
  rnf1 [] = ()
  rnf1 (x : xs) = rnf x `seq` rnf1 xs
