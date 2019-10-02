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
import Data.Functor.Coyoneda

import qualified Control.DeepSeq as DS

class NFData1 (f :: * -> *) where
  liftRnf :: forall x . (x -> ()) -> (f x -> ())
  default liftRnf ::
    forall x . (Generic1 f, NFData1 (Rep1 f)) => (x -> ()) -> f x -> ()
  liftRnf f = liftRnf f . from1

rnf1 :: forall f x . (NFData1 f, NFData x) => f x -> ()
rnf1 = liftRnf rnf

class NFData_ (f :: * -> *) where
  {-| Reduce data structure to normal form while leaving its content untouched. -}
  rnf_ :: forall x . f x -> ()
  default rnf_ ::
    forall x . (Generic1 f, NFData_ (Rep1 f)) => f x -> ()
  rnf_ = rnf_ . from1

--instance {-# INCOHERENT #-} (NFData1 f) => NFData_ f where
--  rnf_ = liftRnf (const ())

class NFData (a :: *) where
  rnf :: a -> ()
  default rnf :: (Generic a, NFData_ (Rep a)) => a -> ()
  rnf = rnf_ @_ @() . from

instance {-# INCOHERENT #-} (NFData1 f, NFData x) => NFData (f x) where
  rnf = rnf1

rwhnf :: a -> ()
rwhnf = DS.rwhnf

deepseq :: NFData a => a -> b -> b
deepseq a b = rnf a `seq` b
force :: NFData a => a -> a
force a = a `deepseq` a

deepseq_ :: NFData_ f => f a -> b -> b
deepseq_ fa b = rnf_ fa `seq` b
force_ :: NFData_ f => f a -> f a
force_ fa = fa `deepseq_` fa

-----------------

instance NFData1 V1 where
  liftRnf f x = case x of {}
instance NFData_ V1 where
  rnf_ x = case x of {}

instance NFData1 U1 where
  liftRnf f U1 = ()
instance NFData_ U1 where
  rnf_ U1 = ()

instance NFData1 Par1 where
  liftRnf f (Par1 x) = f x
instance NFData_ Par1 where
  rnf_ (Par1 x) = ()

instance (NFData1 f) => NFData1 (Rec1 f) where
  liftRnf f (Rec1 fx) = liftRnf f fx
instance (NFData_ f) => NFData_ (Rec1 f) where
  rnf_ (Rec1 fx) = rnf_ fx

instance (NFData a) => NFData1 (K1 i a) where
  liftRnf f (K1 a) = rnf a
instance (NFData a) => NFData_ (K1 i a) where
  rnf_ (K1 a) = rnf a

instance (NFData1 f) => NFData1 (M1 i c f) where
  liftRnf f (M1 fx) = liftRnf f fx
instance (NFData_ f) => NFData_ (M1 i c f) where
  rnf_ (M1 fx) = rnf_ fx

instance (NFData1 f, NFData1 g) => NFData1 (f :+: g) where
  liftRnf f (L1 fx) = liftRnf f fx
  liftRnf f (R1 gx) = liftRnf f gx
instance (NFData_ f, NFData_ g) => NFData_ (f :+: g) where
  rnf_ (L1 fx) = rnf_ fx
  rnf_ (R1 gx) = rnf_ gx

instance (NFData1 f, NFData1 g) => NFData1 (f :*: g) where
  liftRnf f (fx :*: gx) = liftRnf f fx `seq` liftRnf f gx
instance (NFData_ f, NFData_ g) => NFData_ (f :*: g) where
  rnf_ (fx :*: gx) = rnf_ fx `seq` rnf_ gx

instance (NFData1 g, NFData1 f) => NFData1 (g :.: f) where
  liftRnf f (Comp1 gfx) = liftRnf (liftRnf f) gfx
instance (NFData_ g) => NFData_ (g :.: f) where
  rnf_ (Comp1 gfx) = rnf_ gfx

instance (NFData1 g, NFData1 f) => NFData1 (Compose g f) where
  liftRnf f (Compose gfx) = liftRnf (liftRnf f) gfx
instance (NFData1 g, NFData_ f) => NFData_ (Compose g f) where
  rnf_ (Compose gfx) = liftRnf rnf_ gfx

---------------------------------

instance NFData Char where rnf = rwhnf
instance NFData () where rnf = rwhnf
instance NFData Int where rnf = rwhnf
instance NFData Bool where rnf = rwhnf

deriving instance NFData Void

deriving anyclass instance (NFData (g (f v))) => NFData ((Compose g f) v)

---------------------------------

instance NFData1 Identity where
  liftRnf f (Identity x) = f x

deriving instance NFData1 Maybe

instance NFData1 [] where
  liftRnf f [] = ()
  liftRnf f (x : xs) = f x `seq` liftRnf f xs
deriving instance NFData_ []

instance NFData a => NFData1 (Const a) where
  liftRnf f (Const a) = rnf a
instance NFData a => NFData_ (Const a) where
  rnf_ (Const a) = rnf a

instance NFData_ f => NFData_ (Coyoneda f) where
  rnf_ (Coyoneda q fa) = rwhnf q `seq` rnf_ fa
