module Menkar.Analyzer.Syntax where

import Menkar.Analyzer.Class
import Menkar.System.Analyzer
import Menkar.Fine.Syntax
import Menkar.Fine.Context

import GHC.Generics
import Data.Functor.Const

-------------------------

instance (SysAnalyzer sys) => Analyzable sys (ModedModality sys) where
  type Classif (ModedModality sys) = Mode sys -- the codomain
  type Relation (ModedModality sys) = Const ModRel
  analyze token h gamma (MaybeClassified (ModedModality ddom mu) maybeDCod maybeRel) = Just $ do
    rddom <- h id gamma (MaybeClassified ddom (Just U1) (Just U1)) (AddressInfo ["domain"] True)
    rmu   <- h id gamma (MaybeClassified mu ((ddom :*:) <$> maybeDCod) maybeRel) (AddressInfo ["modality"] True)
    return $ case token of
        TokenSubterms -> Box1 $ ModedModality (unbox1 rddom) (unbox1 rmu)
        TokenTypes -> case unboxClassif rmu of
          (ddom' :*: dcod') -> BoxClassif $ dcod'
