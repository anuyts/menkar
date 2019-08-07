{-# LANGUAGE AllowAmbiguousTypes #-}

module Menkar.Analyzer.Solvable where

import Menkar.Basic.Context
import Menkar.Fine.Syntax
import Menkar.Fine.Context
import Menkar.System.Fine
import Menkar.Analyzer.Class
import Menkar.System.Analyzer
import Menkar.Analyzer.Syntax

import Data.Functor.Coerce
import Data.Omissible
import Control.Exception.AssertFalse

import Control.Lens
import Data.Kind hiding (Type)
import Data.Void
import Data.Functor.Identity
import Data.Functor.Compose
import GHC.Generics
import Data.Maybe
import Control.Monad

-----------------------------------

instance SysAnalyzer sys => Solvable sys (Term sys) where
  astAlreadyChecked t ty = Expr2 $ TermAlreadyChecked t ty
  unMeta (Expr2 (TermMeta neut meta (Compose depcies) maybeAlg)) = Just (neut, meta, depcies)
  unMeta _ = Nothing
