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
          ddom <- newMetaMode Nothing gamma "Inferring domain of modality."
          dcod <- newMetaMode Nothing gamma "Inferring codomain of modality."
          return $ AnnotModality $ wrapInChainModty ddom dcod mu
      _   -> scopeFail $ "Illegal annotation: " ++ (render
               (Raw.unparse' qstring \\\ (maybeToList $ Raw.unparse' <$> maybeRawArg))
               $? id
             )
  newMetaMode maybeParent gamma reason = newMetaTermNoCheck maybeParent gamma MetaBlocked Nothing reason
  newMetaModty maybeParent gamma reason = do
    ddom <- newMetaMode Nothing gamma "Inferring domain of modality."
    dcod <- newMetaMode Nothing gamma "Inferring codomain of modality."
    wrapInChainModty ddom dcod <$> newMetaTermNoCheck maybeParent gamma MetaBlocked Nothing reason
