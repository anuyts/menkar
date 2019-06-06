{-# LANGUAGE UndecidableInstances #-}

module Menkar.Systems.Reldtt.Analyzer where

import Menkar.Fine
import Menkar.System
import Menkar.Systems.Reldtt.Fine
import Menkar.Analyzer

import Control.Exception.AssertFalse
import Data.Constraint.Witness

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
  AnTokenReldttMode :: ReldttAnalyzableToken ReldttMode
  AnTokenChainModty :: ReldttAnalyzableToken ChainModty
  AnTokenReldttDegree :: ReldttAnalyzableToken ReldttDegree
  AnTokenReldttSysTerm :: ReldttAnalyzableToken ReldttSysTerm
  AnTokenReldttUniHSConstructor :: ReldttAnalyzableToken ReldttUniHSConstructor

instance Analyzable Reldtt ReldttMode where
  type ClassifExtraInput ReldttMode = U1
  type Classif ReldttMode = U1
  type Relation ReldttMode = U1
  analyzableToken = AnTokenSys $ AnTokenReldttMode
  witClassif token = Witness

  convRel token d = U1
  extraClassif t extraT = U1

instance Analyzable Reldtt ChainModty where
  type ClassifExtraInput ChainModty = U1
  type Classif ChainModty = ReldttMode :*: ReldttMode
  type Relation ChainModty = Const ModRel
  analyzableToken = AnTokenSys $ AnTokenChainModty
  witClassif token = Witness

  convRel token d = U1 :*: U1
  extraClassif t extraT = U1 :*: U1

instance Analyzable Reldtt ReldttDegree where
  type ClassifExtraInput ReldttDegree = U1
  type Classif ReldttDegree = ReldttMode
  type Relation ReldttDegree = Const ModRel
  analyzableToken = AnTokenSys $ AnTokenReldttDegree
  witClassif token = Witness

  convRel token d = U1
  extraClassif t extraT = U1

instance Analyzable Reldtt ReldttSysTerm where
  type ClassifExtraInput ReldttSysTerm = ClassifExtraInput (Term Reldtt)
  type Classif ReldttSysTerm = Classif (Term Reldtt)
  type Relation ReldttSysTerm = Relation (Term Reldtt)
  analyzableToken = AnTokenSys $ AnTokenReldttSysTerm
  witClassif token = Witness

  convRel token d = modedEqDeg d
  extraClassif t extraT = U1

instance Analyzable Reldtt ReldttUniHSConstructor where
  type ClassifExtraInput ReldttUniHSConstructor = ClassifExtraInput (UniHSConstructor Reldtt)
  type Classif ReldttUniHSConstructor = Classif (UniHSConstructor Reldtt)
  type Relation ReldttUniHSConstructor = Relation (UniHSConstructor Reldtt)
  analyzableToken = AnTokenSys $ AnTokenReldttUniHSConstructor
  witClassif token = Witness

  convRel token d = U1
  extraClassif t extraT = U1

instance SysAnalyzer Reldtt where
  quickEqSysUnanalyzable sysError t1 t2 extraT1 extraT2 = case sysError of {}
