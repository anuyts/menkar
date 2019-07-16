module Menkar.Systems.Reldtt.Scoper where

import Menkar.Fine
import Menkar.System
import Menkar.Systems.Reldtt.Fine
import Menkar.Monad
import qualified Menkar.Raw as Raw
import qualified Menkar.PrettyPrint.Raw as Raw
import Menkar.Scoper
import Menkar.Systems.Reldtt.Analyzer

import Text.PrettyPrint.Tree
import Data.Omissible

import Data.Maybe
import Data.Functor.Compose
import Data.Functor.Coerce
import GHC.Generics

instance SysScoper Reldtt where
  scopeAnnotation gamma qstring maybeRawArg = do
    let dgamma' = ctx'mode gamma
    case qstring of
      Raw.Qualified [] "d" -> case maybeRawArg of
        Nothing -> scopeFail $ "Annotation `d` requires an argument."
        Just rawArg -> AnnotMode . ReldttMode <$> expr (crispModedModality dgamma' :\\ gamma) rawArg
      Raw.Qualified [] "m" -> case maybeRawArg of
        Nothing -> scopeFail $ "Annotation `m` requires an argument."
        Just rawArg -> do
          mu <- expr (crispModedModality dgamma' :\\ gamma) rawArg
          ddom <- newMetaModeNoCheck gamma "Inferring domain of modality."
          dcod <- newMetaModeNoCheck gamma "Inferring codomain of modality."
          return $ AnnotModality $ wrapInChainModty ddom dcod mu
      _   -> scopeFail $ "Illegal annotation: " ++ (render
               (Raw.unparse' qstring \\\ (maybeToList $ Raw.unparse' <$> maybeRawArg))
               $? id
             )
  newMetaModeNoCheck gamma reason = ReldttMode !<$> newMetaTermNoCheck gamma MetaBlocked Nothing reason
  newMetaModtyNoCheck gamma reason = do
    dom <- newMetaModeNoCheck gamma "Inferring domain of modality."
    cod <- newMetaModeNoCheck gamma "Inferring codomain of modality."
    tmu <- newMetaTermNoCheck gamma MetaBlocked Nothing reason
    --(meta, depcies) <- newMetaID gamma reason
    return $ wrapInChainModty dom cod tmu
      --ChainModtyMeta ddom dcod meta (Compose depcies)
    --Expr2 (TermMeta )
    --wrapInChainModty ddom dcod <$> newMetaTermNoCheck maybeParent gamma MetaBlocked Nothing reason

  newMetaClassif4sysASTNoCheck sysToken gamma t extraT reason =
    case (sysToken, t) of
      (AnTokenModeTerm, _) -> return U1
      (AnTokenModtyTerm, _) -> do
        dom <- newMetaModeNoCheck gamma reason
        cod <- newMetaModeNoCheck gamma reason
        return $ dom :*: cod
      (AnTokenKnownModty, _) -> do
        dom <- newMetaModeNoCheck gamma reason
        cod <- newMetaModeNoCheck gamma reason
        return $ dom :*: cod
      (AnTokenModtySnout, _) -> return U1
      (AnTokenModtyTail, _) -> do
        dom <- newMetaModeNoCheck gamma reason
        cod <- newMetaModeNoCheck gamma reason
        return $ dom :*: cod
