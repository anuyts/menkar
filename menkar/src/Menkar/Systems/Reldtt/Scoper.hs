module Menkar.Systems.Reldtt.Scoper where

import Menkar.Fine
import Menkar.System
import Menkar.Systems.Reldtt.Fine
import Menkar.Monad
import qualified Menkar.Raw as Raw
import qualified Menkar.PrettyPrint.Raw as Raw
import Menkar.PrettyPrint.Fine
import Menkar.PrettyPrint.Aux.Context
import Menkar.Scoper

import Text.PrettyPrint.Tree
import Data.Omissible

import Data.Maybe

instance SysScoper Reldtt where
  scopeAnnotation gamma qstring maybeArg = do
    case qstring of
      Raw.Qualified [] "d" -> AnnotMode . ReldttMode <$> _
      Raw.Qualified [] "m" -> AnnotModality . ReldttModality <$> _
      _   -> scopeFail $ "Illegal annotation: " ++ (render
               (Raw.unparse' qstring \\\ (maybeToList $ ($? id) . fine2pretty (ctx2scCtx gamma) <$> maybeArg))
               $? id
             )
  newMetaMode maybeParent gamma reason = ReldttMode <$> newMetaTermNoCheck maybeParent gamma MetaBlocked Nothing reason
  newMetaModty maybeParent gamma reason = ReldttModality <$> newMetaTermNoCheck maybeParent gamma MetaBlocked Nothing reason

-- Leave it to the annotation scoper what to do with the annotation!
