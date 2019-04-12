{-# LANGUAGE UndecidableInstances #-}

module Menkar.Analyzer.Syntax where

import Menkar.Analyzer.Class
import Menkar.System.Analyzer
import Menkar.Fine.Syntax
import Menkar.Fine.Context

import Data.Functor.Functor1

import GHC.Generics
import Data.Functor.Const
import Control.Lens

-------------------------

instance (SysAnalyzer sys) => Analyzable sys (ModedModality sys) where
  type Classif (ModedModality sys) = Mode sys -- the codomain
  type Relation (ModedModality sys) = Const ModRel
  analyze token fromType h gamma (MaybeClassified (ModedModality ddom mu) maybeDCod maybeRel) = Just $ do
    rddom <- h id gamma (MaybeClassified ddom (Just U1) (Just U1)) (AddressInfo ["domain"] True)
    rmu   <- h id gamma (MaybeClassified mu ((ddom :*:) <$> maybeDCod) maybeRel) (AddressInfo ["modality"] True)
    return $ case token of
        TokenSubterms -> Box1 $ ModedModality (unbox1 rddom) (unbox1 rmu)
        TokenTypes -> case unboxClassif rmu of
          (ddom' :*: dcod') -> BoxClassif $ dcod'

instance (SysAnalyzer sys,
          Analyzable sys (Type sys),
          Analyzable sys (rhs sys),
          Analyzable sys (Segment Type sys),
          Relation (Type sys) ~ ModedDegree sys,
          Relation (rhs sys) ~ ModedDegree sys,
          Relation (Segment Type sys) ~ ModedDegree sys) => Analyzable sys (Binding Type rhs sys) where
  type Classif (Binding Type rhs sys) = Classif (Segment Type sys) :*: (Classif (rhs sys) :.: VarExt)
  type Relation (Binding Type rhs sys) = ModedDegree sys
  analyze token fromType h gamma (MaybeClassified (Binding seg body) maybeCl maybeDDeg) = Just $ do
    rseg <- h id gamma
      (MaybeClassified seg (fst1 <$> maybeCl) maybeDDeg)
      (AddressInfo ["segment"] False)
    rbody <- h VarWkn (gamma :.. VarFromCtx <$> (decl'content %~ fromType) seg)
      (MaybeClassified body (unComp1 . snd1 <$> maybeCl) (fmap VarWkn <$> maybeDDeg))
      (AddressInfo ["body"] False)
    return $ case token of
      TokenSubterms -> Box1 $ Binding (unbox1 rseg) (unbox1 rbody)
      TokenTypes -> BoxClassif $ unboxClassif rseg :*: Comp1 (unboxClassif rbody)
