module Menkar.System.Scoper where

import Menkar.Fine
import Menkar.Monad
import qualified Menkar.Raw.Syntax as Raw

import Data.Void

class SysSyntax (Term sys) sys => SysScoper sys where
  scopeAnnotation :: (MonadScoper sys sc, DeBruijnLevel v) => Ctx Type sys v Void -> 
    Raw.Qualified String -> Maybe (Term sys v) -> sc (Annotation sys v)
  newMetaMode :: (MonadScoper sys sc) =>
    Maybe (Constraint sys) -> Ctx Type sys v Void -> String -> sc (Mode sys v)
  newMetaModty :: (MonadScoper sys sc) =>
    Maybe (Constraint sys) -> Ctx Type sys v Void -> String -> sc (Modality sys v)

newMetaModedModality :: (SysScoper sys, MonadScoper sys sc, DeBruijnLevel v) =>
  Maybe (Constraint sys) ->
  Ctx Type sys v Void ->
  String ->
  sc (ModedModality sys v)
newMetaModedModality parent gamma reason = do
  d <- newMetaMode parent gamma reason
  mu <- newMetaModty parent gamma reason
  return $ ModedModality d mu
