module Menkar.System.Scoper where

import Menkar.Fine
import Menkar.Monad
import qualified Menkar.Raw.Syntax as Raw
--import Menkar.Analyzer

import Data.Void
import GHC.Generics

class SysSyntax (Term sys) sys => SysScoper sys where
  scopeAnnotation :: (MonadScoper sys sc, DeBruijnLevel v) => Ctx Type sys v Void -> 
    Raw.Qualified String -> Maybe (Raw.Expr) -> sc (Annotation sys v)
  newMetaModeNoCheck :: (MonadScoper sys sc, DeBruijnLevel v) =>
    Maybe (Constraint sys) -> Ctx Type sys v Void -> String -> sc (Mode sys v)
  newMetaModtyNoCheck :: (MonadScoper sys sc, DeBruijnLevel v) =>
    Maybe (Constraint sys) -> Ctx Type sys v Void -> String -> sc (Modality sys v)

newMetaModedModalityNoCheck :: (SysScoper sys, MonadScoper sys sc, DeBruijnLevel v) =>
  Maybe (Constraint sys) ->
  Ctx Type sys v Void ->
  String ->
  sc (ModedModality sys v)
newMetaModedModalityNoCheck parent gamma reason = do
  dom <- newMetaModeNoCheck parent gamma reason
  cod <- newMetaModeNoCheck parent gamma reason
  mu <- newMetaModtyNoCheck parent gamma reason
  return $ ModedModality dom cod mu

{-
newMetaClassifNoCheck :: forall sys sc t v .
  (MonadScoper sys sc, DeBruijnLevel v, SysScoper sys, SysAnalyzer sys, Analyzable sys t) =>
  AnalyzableToken sys t ->
  Maybe (Constraint sys) ->
  Ctx Type sys v Void ->
  String ->
  sc (Classif t v)
newMetaClassifNoCheck token maybeParent gamma reason = case token of
  AnTokenModedModality -> do
    dom <- newMetaModeNoCheck maybeParent gamma reason
    cod <- newMetaModeNoCheck maybeParent gamma reason
    return $ dom :*: cod
  AnTokenBinding tokenRHS -> do
    return $ _
  _ -> _newMetaClassifNoCheck
-}
