{-# LANGUAGE FlexibleContexts, FlexibleInstances, StandaloneDeriving, RankNTypes, PolyKinds, DeriveFunctor #-}
{-# LANGUAGE MultiParamTypeClasses, UndecidableInstances, PartialTypeSignatures, DeriveGeneric #-}

module Menkar.Syntax.LambdaAppSyntax where

import Menkar.Syntax.Algebra
import Data.Maybe
import Data.Functor.Compose
import qualified Control.Category as C
import qualified Control.Categorical.Functor as C

import GHC.Generics

data LambdaAppSyntax x v = App (x v) (x v) | Lam (x (Maybe v))

instance C.Functor LambdaAppSyntax (NT (->)) (NT (->)) where
  fmap (NT nu) = NT $ \ x -> case x of
    App x1 x2 -> App (nu x1) (nu x2)
    Lam x' -> Lam (nu x')

deriving instance Functor x => Functor (LambdaAppSyntax x)

instance Syntax LambdaAppSyntax where
  absorb (App x1 x2) = App (Compose x1) (Compose x2)
  absorb (Lam x') = Lam $ Compose $ fmap sequenceA x'

deriving instance Generic1 (Term LambdaAppSyntax)
