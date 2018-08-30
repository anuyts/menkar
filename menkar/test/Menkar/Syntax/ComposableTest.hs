{-# LANGUAGE DeriveTraversable, KindSignatures, MultiParamTypeClasses, FlexibleContexts, FlexibleInstances,
StandaloneDeriving, UndecidableInstances, TypeOperators, DeriveGeneric, DefaultSignatures, DeriveAnyClass #-}

module Menkar.Syntax.ComposableTest where

import Menkar.Syntax.Composable
import GHC.Generics
import Test.HUnit
import Test.Picker

data LambdaExpr' v =
  Lam (LambdaExpr (Maybe v)) |
  App (LambdaExpr v) (LambdaExpr v)
  deriving (Functor, Foldable, Traversable, Generic1)

deriving instance Swallows LambdaExpr' LambdaExpr
deriving instance Show v => Show (LambdaExpr' v)
deriving instance Eq v => Eq (LambdaExpr' v)

type LambdaExpr = Expr LambdaExpr'

------------------------------

testTerm1 :: LambdaExpr (LambdaExpr Bool)
testTerm1 = Expr $ Lam $ Expr $ App (Var $ Nothing) (Var $ Just $ Expr $ App (Var False) (Var True))
testTerm1' :: LambdaExpr Bool
testTerm1' = Expr $ Lam $ Expr $ App (Var $ Nothing) (Expr $ App (Var $ Just False) (Var $ Just True))
testPretty1 :: String
testPretty1 = "(x > x `(`False` `True`)`)"

test1 :: Test
test1 = testPretty1 ~: swallow testTerm1 ~?= testTerm1'
