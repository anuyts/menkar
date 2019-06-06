module Menkar.Systems.Reldtt.Scoper where

import Menkar.Fine
import Menkar.System
import Menkar.Systems.Reldtt.Fine
import Menkar.Monad
import qualified Menkar.Raw as Raw
import qualified Menkar.PrettyPrint.Raw as Raw
import Menkar.Scoper

import Text.PrettyPrint.Tree
import Data.Omissible

import Data.Maybe
import Data.Functor.Compose

instance SysScoper Reldtt where
  scopeAnnotation gamma qstring maybeRawArg = do
    let dgamma' = ctx'mode gamma
    case qstring of
      Raw.Qualified [] "d" -> case maybeRawArg of
        Nothing -> scopeFail $ "Annotation `d` requires an argument."
        Just rawArg -> AnnotMode <$> expr (crispModedModality dgamma' :\\ gamma) rawArg
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
  newMetaModeNoCheck gamma reason = newMetaTermNoCheck gamma MetaBlocked Nothing reason
  newMetaModtyNoCheck gamma reason = do
    ddom <- newMetaModeNoCheck gamma "Inferring domain of modality."
    dcod <- newMetaModeNoCheck gamma "Inferring codomain of modality."
    (meta, depcies) <- newMetaID gamma reason
    return $ ChainModtyMeta ddom dcod meta (Compose depcies)
    --Expr2 (TermMeta )
    --wrapInChainModty ddom dcod <$> newMetaTermNoCheck maybeParent gamma MetaBlocked Nothing reason

  newMetaClassif4sysASTNoCheck token gamma t extraT reason = _
