module Data.Functor.Functor1 where

import GHC.Generics

fst1 :: (f :*: g) a -> f a
fst1 (fa :*: ga) = fa

snd1 :: (f :*: g) a -> g a
snd1 (fa :*: ga) = ga

absurd1 :: V1 x -> a
absurd1 v = undefined

