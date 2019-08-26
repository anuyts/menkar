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

class NFData1 (f :: * -> *) where
  rnf1 :: forall x . NFData x => f x -> ()
  default rnf1 ::
    forall x . (NFData x, Generic1 f, NFData1 (Rep1 f)) => f x -> ()
  rnf1 = rnf1 . from1

class NFData (a :: *) where
  rnf :: a -> ()
  default rnf :: (Generic a, NFData1 (Rep a)) => a -> ()
  rnf = rnf1 @_ @() . from

instance (NFData1 f, NFData x) => NFData (f x) where
  rnf = rnf1

rwhnf :: a -> ()
rwhnf = DS.rwhnf

-----------------

instance NFData1 V1 where
  rnf1 x = case x of {}

instance NFData1 U1 where
  rnf1 U1 = ()

instance NFData1 Par1 where
  rnf1 (Par1 x) = rnf x

instance (NFData1 f) => NFData1 (Rec1 f) where
  rnf1 (Rec1 fx) = rnf1 fx

instance (NFData a) => NFData1 (K1 i a) where
  rnf1 (K1 a) = rnf a

instance (NFData1 f) => NFData1 (M1 i c f) where
  rnf1 (M1 fx) = rnf1 fx

instance (NFData1 f, NFData1 g) => NFData1 (f :+: g) where
  rnf1 (L1 fx) = rnf1 fx
  rnf1 (R1 gx) = rnf1 gx

instance (NFData1 f, NFData1 g) => NFData1 (f :*: g) where
  rnf1 (fx :*: gx) = rnf1 fx `seq` rnf1 gx

instance (NFData1 g, NFData1 f) => NFData1 (g :.: f) where
  rnf1 (Comp1 gfx) = rnf1 gfx

instance (NFData1 g, NFData1 f) => NFData1 (Compose g f) where
  rnf1 (Compose gfx) = rnf1 gfx

---------------------------------

instance NFData Char where rnf = rwhnf
instance NFData () where rnf = rwhnf
instance NFData Int where rnf = rwhnf
instance NFData Bool where rnf = rwhnf

deriving instance NFData Void

---------------------------------

instance NFData1 Identity where
  rnf1 (Identity x) = rnf x

deriving instance NFData1 Maybe

instance NFData1 [] where
  rnf1 [] = ()
  rnf1 (x : xs) = rnf x `seq` rnf1 xs
