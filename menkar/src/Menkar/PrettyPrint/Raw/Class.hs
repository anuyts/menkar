module Menkar.PrettyPrint.Raw.Class where

import Menkar.Raw.Syntax

import Control.Exception.AssertFalse
import Text.PrettyPrint.Tree
import Data.Omissible

import Data.Maybe

class Unparsable x where
  unparse' :: x -> PrettyTree String
  parserName :: x -> String
  unparse :: x -> String
  unparse x = render (unparse' x) $? id
  showUnparsable :: x -> String
  showUnparsable x = "(quickParse (manySpace *> " ++ parserName x ++ " <* eof) \"\n" ++ unparse x ++ "\n\")"
