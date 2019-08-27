{-# LANGUAGE UndecidableSuperClasses #-}

module Data.Constraint.Image where

class (c (Preimage x), x ~ f (Preimage x)) => Before f c x where
  type Preimage x

instance (c y) => Before f c (f y) where
  type Preimage (f y) = y
