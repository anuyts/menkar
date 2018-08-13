{-# LANGUAGE FlexibleContexts, FlexibleInstances, StandaloneDeriving, RankNTypes, PolyKinds, DeriveFunctor #-}
{-# LANGUAGE MultiParamTypeClasses, UndecidableInstances, PartialTypeSignatures #-}

module Menkar.SyntaxAlgebra where

import Data.Functor.Compose
import qualified Control.Category as C
import qualified Control.Categorical.Functor as C

------------------------

{-| Natural transformations from 'f' to 'g' with codomain category 'cod'
-}
newtype NT cod f g = NT {runNT :: (forall a. cod (f a) (g a))}

{-| If 'cod' is a category, then functors to 'cod' constitute the category 'NT cod'
-}
instance C.Category cod => C.Category (NT cod) where
  id = NT C.id
  NT nu . NT mu = NT (nu C.. mu)

{-| If @dom@ is a kind and 'cod' is a category, then @NT cod f@ is a functor @(dom -> cod) -> *@.
-}
instance C.Category cod => C.Functor (NT cod f) (NT cod) (->) where
  fmap (NT nu) (NT mu) = NT (nu C.. mu)

------------------------

{-| Class meant to define syntaxes. If @Syntax f@ is satisfied, then
    @f :: (* -> *) -> (* -> *)@ defines a syntax in the sense that
    @f x v@ is the type of height n+1 non-variable expressions with variables in 'v',
    if @x v@ is the type of height n non-variable expressions with variables in 'v'.
-}
class (C.Functor f (NT (->)) (NT (->)), Functor (f (Term f))) => Syntax f where
  absorb :: (Functor x, Applicative y) => f x (y v) -> f (Compose x y) v

{-| 'Term' has kind @((* -> *) -> (* -> *)) -> (* -> *)@. The type argument 'f'
    defines the syntax.
    @Term f v@ is then the type of expressions with variables in 'v'.
-}
data Term f v =
  Op (f (Term f) v) |
  Var v

{-| 'Term' is natural in its second argument (the type of variables).
-}
deriving instance Syntax f => Functor (Term f)

{-| 'Term' is natural in its first argument.
-}
fmapTerm :: (Syntax f, Syntax g) => NT (NT (->)) f g -> NT (->) (Term f) (Term g)
fmapTerm (NT nu) = NT $ \ x -> case x of
  Var v -> Var v
  Op ftv -> Op $ runNT nu $
    let tnu = fmapTerm (NT nu)
        --ftnu :: forall f . C.Functor f (NT (->)) (NT (->)) => NT (->) (f (Term _)) (f (Term _))
        ftnu = C.fmap tnu
    in runNT ftnu ftv
{- Could not declare instance, as @(NT (->))@ also considers non-functors as its objects.
instance C.Functor Term (NT (NT (->))) (NT (->)) where
  fmap (NT nu) = NT $ \ x -> case x of
    Var v -> Var v
    Op ftv -> Op $ runNT nu $ _
-}
  
flattenTerm :: Syntax f => Term f (Term f v) -> Term f v
flattenTerm (Var tv) = tv
flattenTerm (Op ftv) = Op $ runNT (C.fmap $ NT $ \ (Compose ttv) -> flattenTerm ttv) $ absorb ftv

instance Syntax f => Applicative (Term f) where
  pure = Var
  f <*> a = flattenTerm $ fmap (<$> a) f

instance Syntax f => Monad (Term f) where
  a >>= f = flattenTerm $ fmap f a

------------------------
