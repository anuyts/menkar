module Data.Constraint.Conditional where

data Conditional c a = Conditional {runConditional :: c => a}

deriving instance Functor (Conditional c)

instance Applicative (Conditional c) where
  pure a = Conditional a
  Conditional f <*> Conditional x = Conditional $ f x

instance Monad (Conditional c) where
  return = pure
  Conditional x >>= f = Conditional $ runConditional $ f x
