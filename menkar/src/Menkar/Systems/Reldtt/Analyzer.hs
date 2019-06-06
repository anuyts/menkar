{-# LANGUAGE UndecidableInstances #-}

module Menkar.Systems.Reldtt.Analyzer where

import Menkar.Fine
import Menkar.System
import Menkar.Systems.Reldtt.Fine
import Menkar.Analyzer

import Control.Exception.AssertFalse

import GHC.Generics
import Util
import Data.Functor.Compose
import Data.Functor.Const
import Control.Lens
import Data.Kind hiding (Type)

type instance SysAnalyzerError Reldtt = ReldttAnalyzerError
type instance SysAnalyzableToken Reldtt = ReldttAnalyzableToken

data ReldttAnalyzerError where
data ReldttAnalyzableToken (t :: * -> *) where

instance Analyzable Reldtt ReldttMode where
  type ClassifExtraInput ReldttMode = U1
  type Classif ReldttMode = U1
  type Relation ReldttMode = U1

instance Analyzable Reldtt ChainModty where
  type ClassifExtraInput ChainModty = U1
  type Classif ChainModty = ReldttMode :*: ReldttMode
  type Relation ChainModty = Const ModRel

instance Analyzable Reldtt ReldttDegree where
  type ClassifExtraInput ReldttDegree = U1
  type Classif ReldttDegree = ReldttMode
  type Relation ReldttDegree = Const ModRel

instance Analyzable Reldtt ReldttSysTerm where
  type ClassifExtraInput ReldttSysTerm = ClassifExtraInput (Term Reldtt)
  type Classif ReldttSysTerm = Classif (Term Reldtt)
  type Relation ReldttSysTerm = Relation (Term Reldtt)

instance Analyzable Reldtt ReldttUniHSConstructor where
  type ClassifExtraInput ReldttUniHSConstructor = ClassifExtraInput (UniHSConstructor Reldtt)
  type Classif ReldttUniHSConstructor = Classif (UniHSConstructor Reldtt)
  type Relation ReldttUniHSConstructor = Relation (UniHSConstructor Reldtt)

instance SysAnalyzer Reldtt where
  quickEqSysUnanalyzable sysError t1 t2 extraT1 extraT2 = _
