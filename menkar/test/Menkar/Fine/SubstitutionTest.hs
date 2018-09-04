{-# LANGUAGE DeriveTraversable, KindSignatures, MultiParamTypeClasses, FlexibleContexts, FlexibleInstances,
StandaloneDeriving, UndecidableInstances, TypeOperators, DeriveGeneric, DefaultSignatures, DeriveAnyClass #-}

module Menkar.Fine.SubstitutionTest where

import Menkar.Fine.Substitution
import GHC.Generics
import Test.HUnit
import Test.Picker

------------------------------

instance (Pickable v, Pickable (e v)) => Pickable (Expr e v) where
  picker = chooseDeeper [Var <$> picker] [Expr <$> picker]

------------------------------

data LambdaExpr' v =
  Lam (LambdaExpr (Maybe v)) |
  App (LambdaExpr v) (LambdaExpr v)
  deriving (Functor, Foldable, Traversable, Generic1, CanSwallow LambdaExpr)

--deriving instance CanSwallow LambdaExpr LambdaExpr'
deriving instance Show v => Show (LambdaExpr' v)
deriving instance Eq v => Eq (LambdaExpr' v)

type LambdaExpr = Expr LambdaExpr'

instance (Pickable v) => Pickable (LambdaExpr' v) where
  picker = choose [Lam <$> picker, App <$> picker <*> picker]

------------------------------

testTerm1 :: LambdaExpr (LambdaExpr Bool)
testTerm1 = Expr $ Lam $ Expr $ App (Var $ Nothing) (Var $ Just $ Expr $ App (Var False) (Var True))
testTerm1' :: LambdaExpr Bool
testTerm1' = Expr $ Lam $ Expr $ App (Var $ Nothing) (Expr $ App (Var $ Just False) (Var $ Just True))
testPretty1 :: String
testPretty1 = "(x > x `(`False` `True`)`)"

test1 :: Test
test1 = testPretty1 ~: swallow testTerm1 ~?= testTerm1'
