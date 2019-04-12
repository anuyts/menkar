{-# LANGUAGE UndecidableInstances #-}

module Menkar.Analyzer.Syntax where

import Menkar.Analyzer.Class
import Menkar.System.Analyzer
import Menkar.Fine.Syntax
import Menkar.Fine.Context
import Menkar.System.Fine.Multimode

import Data.Functor.Functor1

import GHC.Generics
import Data.Functor.Const
import Control.Lens
import Data.Functor.Compose
import Control.Monad
import Data.Void

-------------------------

instance (SysAnalyzer sys) => Analyzable sys (ModedModality sys) where
  type Classif (ModedModality sys) = Mode sys :*: Mode sys -- domain and codomain
  type Relation (ModedModality sys) = Const ModRel
  analyze token fromType h gamma (MaybeClassified (ModedModality ddom dcod mu) _ maybeRel) = Just $ do
    rddom <- h id gamma (MaybeClassified ddom (Just U1) (toIfRelate token U1)) (AddressInfo ["domain"] True)
    rdcod <- h id gamma (MaybeClassified dcod (Just U1) (toIfRelate token U1)) (AddressInfo ["codomain"] True)
    rmu   <- h id gamma (MaybeClassified mu (Just $ ddom :*: dcod) maybeRel) (AddressInfo ["modality"] True)
    return $ case token of
        TokenSubterms -> Box1 $ ModedModality (unbox1 rddom) (unbox1 rdcod) (unbox1 rmu)
        TokenTypes -> BoxClassif $ ddom :*: dcod
        TokenRelate -> Unit2

instance (SysAnalyzer sys,
          Analyzable sys (rhs sys),
          Relation (rhs sys) ~ ModedDegree sys
         ) => Analyzable sys (Binding Type rhs sys) where
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
      TokenRelate -> Unit2

instance (SysAnalyzer sys) => Analyzable sys (UniHSConstructor sys) where
  
  type Classif (UniHSConstructor sys) = Compose Maybe (Mode sys) -- a mode if you care
  type Relation (UniHSConstructor sys) = ModedDegree sys
  
  analyze (token :: AnalyzerToken option) fromType h
    (gamma :: Ctx lhs sys v Void) (MaybeClassified ty maybeMaybeD maybeDDeg) = Just $ do
    
    let dgamma' = ctx'mode gamma
    let dgamma = unVarFromCtx <$> dgamma'

    case ty of
      
      UniHS d -> do
        rd <- h id (crispModedModality dgamma' :\\ gamma)
          (MaybeClassified d (Just U1) (toIfRelate token U1))
          (AddressInfo ["mode"] False)
        return $ case token of
          TokenSubterms -> Box1 $ UniHS (unbox1 rd)
          TokenTypes -> BoxClassif $ Compose $ Just $ d
          TokenRelate -> Unit2

      Pi binding -> handleBinder Pi binding

      Sigma binding -> handleBinder Sigma binding

      EmptyType -> handleConstant

    where handleBinder ::
            (Binding Type Term sys v -> UniHSConstructor sys v) -> Binding Type Term sys v ->
            _ (AnalyzerResult option (UniHSConstructor sys) v)
          handleBinder binder binding = do
            let bindingClassif = case maybeMaybeD of
                  Nothing -> Nothing
                  Just (Compose Nothing) -> Nothing
                  Just (Compose (Just d)) -> Just $ U1 :*: Comp1 (hs2type $ UniHS $ VarWkn <$> d)
            rbinding <- h id gamma
              (MaybeClassified binding bindingClassif maybeDDeg)
              (AddressInfo ["binding"] False)
            return $ case token of
              TokenSubterms -> Box1 $ binder $ unbox1 rbinding
              TokenTypes -> BoxClassif $ Compose Nothing
              TokenRelate -> Unit2
              
          handleConstant = pure $ case token of
            TokenSubterms -> Box1 $ ty
            TokenTypes -> BoxClassif $ Compose Nothing
            TokenRelate -> Unit2

instance SysAnalyzer sys => Analyzable sys (Type sys) where
  type Classif (Type sys) = U1
  type Relation (Type sys) = ModedDegree sys

instance SysAnalyzer sys => Analyzable sys (Term sys) where
  type Classif (Term sys) = Type sys
  type Relation (Term sys) = ModedDegree sys

instance SysAnalyzer sys => Analyzable sys (Segment Type sys) where
  type Classif (Segment Type sys) = Classif (Type sys)
  type Relation (Segment Type sys) = ModedDegree sys
