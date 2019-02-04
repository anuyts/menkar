module Data.Omissible where

{-| In order to give a function optional arguments, give it a last argument of an @'Omissible'@ type @Options@.
    Options can then be set via lenses on @Options@.

    Assume a 3-argument function @f :: X -> Y -> Z -> Options -> Result@ with lenses
    @recursive :: ASetter' Options Bool@
    @verbose :: ASetter' Options Bool@

    To call @f@ with default options:
    @f x y z $? id@
    To call @f@ with mostly default options, but verbosely and recursively:
    @f x y z $? verbose .~ True &? recursive .~ True@
    To call @f@ with options @opts@:
    @f x y z $ opts@
    To call @f@ with options @opts@, but verbosely and recursively:
    @f x y z $ opts & verbose .~ True &? recursive .~ True@
-}
class Omissible a where
  omit :: a

($?) :: Omissible a => (b -> c) -> (a -> b) -> c
f $? g = f $ g omit
infixr 0 $?

(&?) :: (a -> b) -> (b -> c) -> (a -> c)
f &? g = g . f
infixl 2 &?
