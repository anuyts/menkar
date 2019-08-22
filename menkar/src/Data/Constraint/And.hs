{-# LANGUAGE UndecidableSuperClasses #-}

module Data.Constraint.And where

class (a x, b x) => (a :&: b) x where

instance (a x, b x) => (a :&: b) x where
