{-# LANGUAGE FlexibleContexts, FlexibleInstances, StandaloneDeriving, RankNTypes, PolyKinds, DeriveFunctor #-}
{-# LANGUAGE MultiParamTypeClasses, UndecidableInstances #-}

module SyntaxAlgebra where

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

{-| If @dom@ and 'cod' are categories, then @NT cod f@ is a functor @(dom -> cod) -> *@.
-}
instance C.Category cod => C.Functor (NT cod f) (NT cod) (->) where
  fmap (NT nu) (NT mu) = NT (nu C.. mu)

------------------------

{-| 'Term' has kind @((* -> *) -> (* -> *)) -> (* -> *)@
    @f x v@ is the type of height n+1 non-variable expressions with variables in 'v',
    if @x v@ is the type of height n non-variable expressions.
    @Term f v@ is then the type of expressions with variables in 'v'.
-}
data Term f v =
  Op (f (Term f) v) |
  Var v

{-| 'Term' is natural in its second argument.
-}
deriving instance Functor (f (Term f)) => Functor (Term f)

{-| 'Term' is natural in its first argument.
-}
instance C.Functor Term (NT (NT (->))) (NT (->)) where
  fmap (NT nu) = NT $ \ x -> case x of
    Var v -> Var v
    Op ftv -> Op $ runNT nu $ _

{-
flattenTerm :: Functor (f (Term f)) => Term f (Term f v) -> Term f v
flattenTerm (Var tv) = tv
flattenTerm (Op ftv) = Op $ _ ftv --flattenTerm ftv
-}

{-
instance Functor (f (Term f)) => Applicative (Term f) where
  pure = Var
  f <*> a = _
-}

--instance C.Functor Term NT NT where
--  fmap (NT nu) = NT _
