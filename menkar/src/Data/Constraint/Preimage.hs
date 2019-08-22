{-# LANGUAGE UndecidableSuperClasses #-}

module Data.Constraint.Preimage where

class c (f x) => After f c x where

instance c (f x) => After f c x where
