module Menkar.Syntax.FreeMonad where

import Data.Maybe

data Term_ t = App t t | Lam (Binding_ t) deriving (Functor, Foldable, Traversable)
data Term v = Var v | Term_ (Term v)

data Binding_ t = Binding_ (Type_ t) (Maybe t) deriving (Functor, Foldable, Traversable)

newtype Type_ t = Type_ {unType :: t} deriving (Functor, Foldable, Traversable)
