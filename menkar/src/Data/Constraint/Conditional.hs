module Data.Constraint.Conditional where

import Data.Functor.Identity
--import Control.Monad.Morph

data ConditionalT c m a = ConditionalT {runConditionalT :: c => m a}
type Conditional c = ConditionalT c Identity
-- -- | Doesn't work as a pattern due to constraint.
--pattern Conditional a = ConditionalT (Identity a)
conditional :: (c => a) -> Conditional c a
conditional a = ConditionalT $ Identity a
runConditional :: c => Conditional c a -> a
runConditional = runIdentity . runConditionalT

deriving instance Functor m => Functor (ConditionalT c m)

instance Applicative m => Applicative (ConditionalT c m) where
  pure a = ConditionalT $ pure a
  ConditionalT mf <*> ConditionalT mx = ConditionalT $ mf <*> mx

instance Monad m => Monad (ConditionalT c m) where
  return = pure
  ConditionalT mx >>= f = ConditionalT $ mx >>= (runConditionalT . f)

mmapConditionalT :: (forall x . m x -> n x) -> ConditionalT c m a -> ConditionalT c n a
mmapConditionalT f (ConditionalT ma) = ConditionalT $ f ma

{-
instance MFunctor (ConditionalT c) where
  mmap f (ConditionalT mx) = ConditionalT $ f mx
-}

{-
data Conditional c a = Conditional {runConditional :: c => a}

deriving instance Functor (Conditional c)

instance Applicative (Conditional c) where
  pure a = Conditional a
  Conditional f <*> Conditional x = Conditional $ f x

instance Monad (Conditional c) where
  return = pure
  Conditional x >>= f = Conditional $ runConditional $ f x
-}
