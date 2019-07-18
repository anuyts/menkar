module Menkar.Systems.Reldtt.PrettyPrint.Raw where

import Menkar.Raw
import Menkar.PrettyPrint.Raw
import Menkar.Systems.Reldtt.Basic
import Menkar.Systems.Reldtt.Raw
import Menkar.Systems.Reldtt.PrettyPrint.Basic

import Text.PrettyPrint.Tree

import Control.Lens

instance Unparsable ModtyTailAspect where
  unparse' tail@(ModtyTailAspect str e) = str ++ " " ++| unparse' e
  parserName _ = "modtyTailAspect"

instance Unparsable KnownModty where
  unparse' kmu@(KnownModty snout tail) =
    ribbon ("[" ++ snout2string snout) \\\
      ((" + " ++|) . unparse' <$> _modtyTail'aspects tail) ///
    ribbon "]"
  parserName _ = "sysExprC"

instance SysRawPretty Reldtt where
