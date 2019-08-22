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

class NFData1 (goodarg :: * -> Constraint) (f :: * -> *) | f -> goodarg where
  rnf1 :: goodarg x => f x -> ()
  default rnf1 :: (goodarg' x, Generic1 f, NFData1 goodarg' (Rep1 f)) => f x -> ()
  rnf1 = rnf1 . from1

class NFData (a :: *) where
  rnf :: a -> ()
  default rnf :: (Generic a, NFData1 Unconstrained (Rep a)) => a -> ()
  rnf = rnf1 @Unconstrained . from

instance (NFData1 goodarg f, goodarg x) => NFData (f x) where
  rnf = rnf1 @goodarg

rwhnf :: a -> ()
rwhnf = DS.rwhnf

-----------------

instance NFData1 Unconstrained V1 where
  rnf1 x = case x of {}

instance NFData1 Unconstrained U1 where
  rnf1 U1 = ()

instance NFData1 NFData Par1 where
  rnf1 (Par1 x) = rnf x

instance (NFData1 goodarg f) => NFData1 goodarg (Rec1 f) where
  rnf1 (Rec1 fx) = rnf1 @goodarg fx

instance (NFData a) => NFData1 Unconstrained (K1 i a) where
  rnf1 (K1 a) = rnf a

instance (NFData1 goodarg f) => NFData1 goodarg (M1 i c f) where
  rnf1 (M1 fx) = rnf1 @goodarg fx

instance (NFData1 farg f, NFData1 garg g) => NFData1 (farg :&: garg) (f :+: g) where
  rnf1 (L1 fx) = rnf1 @farg fx
  rnf1 (R1 gx) = rnf1 @garg gx

instance (NFData1 farg f, NFData1 garg g) => NFData1 (farg :&: garg) (f :*: g) where
  rnf1 (fx :*: gx) = rnf1 @farg fx `seq` rnf1 @garg gx

instance (NFData1 goodarg g) => NFData1 (After f goodarg) (g :.: f) where
  rnf1 (Comp1 gfx) = rnf1 @goodarg gfx

instance (NFData1 goodarg g) => NFData1 (After f goodarg) (Compose g f) where
  rnf1 (Compose gfx) = rnf1 @goodarg gfx

---------------------------------

deriving instance NFData Void

instance (NFData (g (f a))) => NFData (Compose g f a) where
  rnf (Compose gfa) = rnf gfa

---------------------------------

instance NFData1 NFData Identity where
  rnf1 (Identity x) = rnf x
