{-# LANGUAGE DataKinds, KindSignatures, GADTs, TypeOperators, RankNTypes #-}

module Menkar.Syntax.Syntax where

import Data.Type.Natural (Nat(..))
import Menkar.Syntax.Core

--Expression: Nothing
data SyntaxPreclass =
  PreclassMode |
  PreclassModality |
  PreclassList SyntaxClass
  --PreclassExpr2
type SyntaxClass = Maybe SyntaxPreclass
type ClassMode = Just PreclassMode
type ClassModality = Just PreclassModality
type ClassExpr = Nothing
type ClassList c = Just (PreclassList c)
--type ClassExpr2 = Just PreclassExpr2

data LamInfo where
data MetaInfo where
  
data (:##>) (arityclasses :: [(Nat, Maybe SyntaxPreclass)]) (cl :: Maybe SyntaxPreclass) :: * where
  -------------------------------------------------------
  -- | # EXPRESSIONS
  -- | domain mode, domain modality, domain, body
  Lam :: LamInfo ->
           '[ '(Z, ClassMode), '(Z, ClassModality), '(Z, ClassExpr), '(S Z, ClassExpr) ] :##> ClassExpr
  App :: '[ '(Z, ClassExpr), '(Z, ClassExpr) ] :##> ClassExpr
  -- | any number of arguments
  Meta :: forall n . MetaInfo -> '[ '(Z, ClassList ClassExpr) ] :##> ClassExpr
  
  -------------------------------------------------------
  -- | # LISTS
  OpNil :: '[] :##> ClassList c
  OpCons :: '[ '(Z, c), '(Z, ClassList c) ] :##> ClassList c
  
  -------------------------------------------------------
  -- Expr2 :: '[ '(Z, ClassExpr), '(Z, ClassExpr) ] :##> ClassExpr2

type Expr v = Term (:##>) ClassExpr v
