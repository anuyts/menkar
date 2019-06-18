{-# LANGUAGE UndecidableInstances #-}

module Menkar.Systems.Reldtt.Analyzer where

import Menkar.Fine
import Menkar.System
import Menkar.Systems.Reldtt.Fine
import Menkar.Analyzer

import Data.Functor.Functor1
import Data.Omissible
import Control.Exception.AssertFalse
import Data.Constraint.Witness
import Data.Constraint.Conditional
import Data.Functor.Coerce

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
  AnTokenKnownModty :: ReldttAnalyzableToken KnownModty

instance Analyzable Reldtt ReldttMode where
  type ClassifExtraInput ReldttMode = U1
  type Classif ReldttMode = U1
  type Relation ReldttMode = U1
  analyzableToken = AnTokenSys $ AnTokenReldttMode
  witClassif token = Witness
  analyze token gamma (Classification (ReldttMode t) U1 maybeU1) h = Right $ do
    rt <- fmapCoe runIdentity <$> h Identity
      (conditional $ ReldttMode unreachable)
      (\ gamma' (Classification (ReldttMode t') U1 maybeU1') ->
         Just $ Identity !<$> Classification t' U1 (ClassifMustBe $ BareSysType $ SysTypeMode))
      extCtxId
      (\ d U1 -> modedEqDeg $ Identity !<$> d)
      (AddressInfo ["underlying term of modality"] FocusWrapped EntirelyBoring)
    return $ case token of
      TokenTrav -> AnalysisTrav $ ReldttMode $ getAnalysisTrav $ rt
      TokenTC -> AnalysisTC $ U1
      TokenRel -> AnalysisRel
  convRel token d = U1
  extraClassif t extraT = U1

{-| Chain modalities need to be whnormalized before comparing them!
-}
instance Analyzable Reldtt ChainModty where
  type ClassifExtraInput ChainModty = U1
  type Classif ChainModty = ReldttMode :*: ReldttMode
  type Relation ChainModty = Const ModRel
  analyzableToken = AnTokenSys $ AnTokenChainModty
  witClassif token = Witness
  
  analyze token gamma (Classification chmu U1 maybeDomCod) h = case chmu of
    
    ChainModtyKnown kmu -> Right $ do
      rkmu <- fmapCoe runIdentity <$> h Identity
        (conditional $ ChainModtyKnown unreachable)
        (\ gamma' -> \ case
            (Classification (ChainModtyKnown kmu') U1 maybeDomCod') ->
              Just $ Identity !<$> Classification kmu' U1 (classifMust2will maybeDomCod')
            otherwise -> Nothing
        )
        extCtxId
        extRelId
        (AddressInfo ["underlying known modality"] FocusWrapped omit)
      return $ case token of
        TokenTrav -> AnalysisTrav $ ChainModtyKnown $ getAnalysisTrav rkmu
        TokenTC -> AnalysisTC $ getAnalysisTC $ rkmu
        TokenRel -> AnalysisRel
        
    ChainModtyLink kmu termNu chainRho -> Right $ do
      rkmu <- fmapCoe runIdentity <$> h Identity
        (conditional $ ChainModtyLink unreachable unreachable unreachable)
        (\ gamma' -> \ case
            (Classification (ChainModtyLink kmu' termNu' chainRho') U1 maybeDomCod') ->
              Just $ Identity !<$> Classification kmu' U1
                (ClassifWillBe (_knownModty'dom kmu' :*: _knownModty'cod kmu'))
            otherwise -> Nothing
        )
        extCtxId
        extRelId
        (AddressInfo ["initial known modality"] FocusWrapped omit)
      rtermNu <- fmapCoe runIdentity <$> h Identity
        (conditional $ ChainModtyLink (getAnalysisTrav rkmu) unreachable unreachable)
        (\ gamma' -> \ case
            (Classification (ChainModtyLink kmu' termNu' chainRho') U1 maybeDomCod') ->
              Just $ Identity !<$> Classification termNu' U1
                (ClassifWillBe $ BareSysType $ SysTypeModty (_chainModty'cod chainRho') (_knownModty'dom kmu'))
            otherwise -> Nothing
        )
        extCtxId
        (\ d rel -> modedEqDeg $ Identity !<$> d)
        (AddressInfo ["first neutral component"] FocusEliminee omit)
      rchainRho <- fmapCoe runIdentity <$> h Identity
        (conditional $ ChainModtyLink (getAnalysisTrav rkmu) (getAnalysisTrav rtermNu) unreachable)
        (\ gamma' -> \ case
            (Classification (ChainModtyLink kmu' termNu' chainRho') U1 maybeDomCod') ->
              Just $ Identity !<$> Classification chainRho' U1
                (ClassifWillBe $ _chainModty'dom chainRho' :*: _chainModty'cod chainRho')
            otherwise -> Nothing
        )
        extCtxId
        extRelId
        (AddressInfo ["tail component"] NoFocus omit)
      return $ case token of
        TokenTrav -> AnalysisTrav $
          ChainModtyLink (getAnalysisTrav rkmu) (getAnalysisTrav rtermNu) (getAnalysisTrav rchainRho)
        TokenTC -> AnalysisTC $ _chainModty'dom chainRho :*: _knownModty'cod kmu
        TokenRel -> AnalysisRel

    ChainModtyDisguisedAsTerm dom cod t -> Right $ do
      rdom <- fmapCoe runIdentity <$> h Identity
        (conditional $ ChainModtyDisguisedAsTerm unreachable unreachable unreachable)
        (\ gamma' -> \ case
            (Classification (ChainModtyDisguisedAsTerm dom' cod' t') U1 maybeDomCod') ->
              Just $ Identity !<$> Classification dom' U1 (ClassifWillBe U1)
            otherwise -> Nothing
        )
        extCtxId
        (\ d rel -> U1)
        (AddressInfo ["domain"] FocusWrapped omit)
      rcod <- fmapCoe runIdentity <$> h Identity
        (conditional $ ChainModtyDisguisedAsTerm unreachable unreachable unreachable)
        (\ gamma' -> \ case
            (Classification (ChainModtyDisguisedAsTerm dom' cod' t') U1 maybeDomCod') ->
              Just $ Identity !<$> Classification cod' U1 (ClassifWillBe U1)
            otherwise -> Nothing
        )
        extCtxId
        (\ d rel -> U1)
        (AddressInfo ["codomain"] FocusWrapped omit)
      rt <- fmapCoe runIdentity <$> h Identity
        (conditional $ ChainModtyDisguisedAsTerm (getAnalysisTrav rdom) (getAnalysisTrav rcod) unreachable)
        (\ gamma' -> \ case
            (Classification (ChainModtyDisguisedAsTerm dom' cod' t') U1 maybeDomCod') ->
              Just $ Identity !<$> Classification t' U1
                (ClassifMustBe $ BareSysType $ SysTypeChainModtyDisguisedAsTerm)
            otherwise -> Nothing
        )
        extCtxId
        (\ d rel -> modedEqDeg $ Identity !<$> d)
        (AddressInfo ["modality disguised as term (probably a meta)"] FocusEliminee omit)
      return $ case token of
        TokenTrav -> AnalysisTrav $
          ChainModtyDisguisedAsTerm (getAnalysisTrav rdom) (getAnalysisTrav rcod) (getAnalysisTrav rt)
        TokenTC -> AnalysisTC $ dom :*: cod
        TokenRel -> AnalysisRel
      
  convRel token d = U1 :*: U1
  extraClassif t extraT = U1 :*: U1

instance Analyzable Reldtt KnownModty where
  type ClassifExtraInput KnownModty = U1
  type Classif KnownModty = ReldttMode :*: ReldttMode
  type Relation KnownModty = Const ModRel
  analyzableToken = AnTokenSys $ AnTokenKnownModty
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

--------------------------------

instance SysAnalyzer Reldtt where
  quickEqSysUnanalyzable sysError t1 t2 extraT1 extraT2 = case sysError of {}
