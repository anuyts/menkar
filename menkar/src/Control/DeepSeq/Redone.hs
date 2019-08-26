{-# LANGUAGE UndecidableInstances, AllowAmbiguousTypes #-}

{-| Reimplementation of NFData, in order to get rid of instance for Compose... -}

module Control.DeepSeq.Redone where

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
import Data.Functor.Const

import qualified Control.DeepSeq as DS

class NFData1 (f :: * -> *) where
  liftRnf :: forall x . (x -> ()) -> (f x -> ())
  default liftRnf ::
    forall x . (Generic1 f, NFData1 (Rep1 f)) => (x -> ()) -> f x -> ()
  liftRnf f = liftRnf f . from1

rnf1 :: forall f x . (NFData1 f, NFData x) => f x -> ()
rnf1 = liftRnf rnf
rnf_ :: forall f x . (NFData1 f) => f x -> ()
rnf_ = liftRnf (const ())

class NFData (a :: *) where
  rnf :: a -> ()
  default rnf :: (Generic a, NFData1 (Rep a)) => a -> ()
  rnf = rnf1 @_ @() . from

instance {-# INCOHERENT #-} (NFData1 f, NFData x) => NFData (f x) where
  rnf = rnf1

rwhnf :: a -> ()
rwhnf = DS.rwhnf
deepseq :: NFData a => a -> b -> b
deepseq a b = rnf a `seq` b
force :: NFData a => a -> a
force a = a `deepseq` a

-----------------

instance NFData1 V1 where
  liftRnf f x = case x of {}

instance NFData1 U1 where
  liftRnf f U1 = ()

instance NFData1 Par1 where
  liftRnf f (Par1 x) = f x

instance (NFData1 f) => NFData1 (Rec1 f) where
  liftRnf f (Rec1 fx) = liftRnf f fx

instance (NFData a) => NFData1 (K1 i a) where
  liftRnf f (K1 a) = rnf a

instance (NFData1 f) => NFData1 (M1 i c f) where
  liftRnf f (M1 fx) = liftRnf f fx

instance (NFData1 f, NFData1 g) => NFData1 (f :+: g) where
  liftRnf f (L1 fx) = liftRnf f fx
  liftRnf f (R1 gx) = liftRnf f gx

instance (NFData1 f, NFData1 g) => NFData1 (f :*: g) where
  liftRnf f (fx :*: gx) = liftRnf f fx `seq` liftRnf f gx

instance (NFData1 g, NFData1 f) => NFData1 (g :.: f) where
  liftRnf f (Comp1 gfx) = liftRnf (liftRnf f) gfx

instance (NFData1 g, NFData1 f) => NFData1 (Compose g f) where
  liftRnf f (Compose gfx) = liftRnf (liftRnf f) gfx

---------------------------------

instance NFData Char where rnf = rwhnf
instance NFData () where rnf = rwhnf
instance NFData Int where rnf = rwhnf
instance NFData Bool where rnf = rwhnf

deriving instance NFData Void

deriving instance (NFData (g (f v))) => NFData ((Compose g f) v)

---------------------------------

instance NFData1 Identity where
  liftRnf f (Identity x) = f x

deriving instance NFData1 Maybe

instance NFData1 [] where
  liftRnf f [] = ()
  liftRnf f (x : xs) = f x `seq` liftRnf f xs

instance NFData a => NFData1 (Const a) where
  liftRnf f (Const a) = rnf a
