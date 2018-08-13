{-# LANGUAGE FlexibleContexts, FlexibleInstances, StandaloneDeriving, RankNTypes, PolyKinds, DeriveFunctor #-}
{-# LANGUAGE MultiParamTypeClasses, UndecidableInstances, PartialTypeSignatures #-}

module Menkar.SyntaxAlgebra.ExampleSyntax where

import Menkar.SyntaxAlgebra
import Data.Maybe
import Data.Functor.Compose
import qualified Control.Category as C
import qualified Control.Categorical.Functor as C

data LambdaSyntax x v = App (x v) (x v) | Lam (x (Maybe v))

instance C.Functor LambdaSyntax (NT (->)) (NT (->)) where
  fmap (NT nu) = NT $ \ x -> case x of
    App x1 x2 -> App (nu x1) (nu x2)
    Lam x' -> Lam (nu x')

deriving instance Functor x => Functor (LambdaSyntax x)

instance Syntax LambdaSyntax where
  absorb (App x1 x2) = App (Compose x1) (Compose x2)
  absorb (Lam x') = Lam $ Compose $ fmap sequenceA x'
