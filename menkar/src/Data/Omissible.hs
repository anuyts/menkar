module Data.Omissible where

class Omissible a where
  omitted :: a

($?) :: Omissible a => (a -> b) -> (a -> a) -> b
f $? g = f $ g omitted
infixr 0 $?

(&?) :: (a -> b) -> (b -> c) -> (a -> c)
f &? g = g . f
infixl 2 &?
