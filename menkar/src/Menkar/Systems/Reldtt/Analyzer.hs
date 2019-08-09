{-# LANGUAGE UndecidableInstances #-}

module Menkar.Systems.Reldtt.Analyzer where

import Menkar.Fine
import Menkar.System
import Menkar.Systems.Reldtt.Basic
import Menkar.Systems.Reldtt.Fine
import Menkar.Analyzer
import Menkar.TC.QuickEq

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
import Data.Functor.Compose
import Data.Functor.Coyoneda

type instance SysAnalyzerError Reldtt = ReldttAnalyzerError
type instance SysAnalyzableToken Reldtt = ReldttAnalyzableToken

data ReldttAnalyzerError =
  AnErrorModtySnout |
  AnErrorChainModtyMeta |
  AnErrorChainModtyAlreadyChecked
data ReldttAnalyzableToken (t :: * -> *) where
  --AnTokenReldttMode :: ReldttAnalyzableToken ReldttMode
  --AnTokenChainModty :: ReldttAnalyzableToken ChainModty
  --AnTokenReldttDegree :: ReldttAnalyzableToken ReldttDegree
  --AnTokenReldttSysTerm :: ReldttAnalyzableToken ReldttSysTerm
  AnTokenModeTerm :: ReldttAnalyzableToken ModeTerm
  AnTokenModtyTerm :: ReldttAnalyzableToken ModtyTerm
  --AnTokenReldttUniHSConstructor :: ReldttAnalyzableToken ReldttUniHSConstructor
  AnTokenKnownModty :: ReldttAnalyzableToken KnownModty
  AnTokenModtySnout :: ReldttAnalyzableToken (Const ModtySnout)
  AnTokenModtyTail :: ReldttAnalyzableToken ModtyTail

instance Analyzable Reldtt ReldttMode where
  type ClassifExtraInput ReldttMode = U1
  type Classif ReldttMode = U1
  type Relation ReldttMode = U1
  analyzableToken = AnTokenMultimode AnTokenMode --AnTokenSys $ AnTokenReldttMode
  witClassif token = Witness
  analyze token gamma (Classification (ReldttMode t) U1 maybeU1) h = Right $ do
    rt <- fmapCoe runIdentity <$> h Identity
      (conditional $ ReldttMode unreachable)
      (\ gamma' (Classification (ReldttMode t') U1 maybeU1') ->
         Just $ Identity !<$> Classification t' U1 (ClassifMustBe $ BareSysType $ SysTypeMode))
      extCtxId
      (\ d _ -> hoistcoy modedEqDeg $ Identity !<$> d)
      (AddressInfo ["underlying term of modality"] FocusWrapped EntirelyBoring)
    return $ case token of
      TokenTrav -> AnalysisTrav $ ReldttMode $ getAnalysisTrav $ rt
      TokenTC -> AnalysisTC $ U1
      TokenRel -> AnalysisRel
  convRel token d = U1
  extraClassif d t extraT = U1

{-| Chain modalities need to be whnormalized before comparing them!
-}
instance Analyzable Reldtt ChainModty where
  type ClassifExtraInput ChainModty = U1
  type Classif ChainModty = ReldttMode :*: ReldttMode
  type Relation ChainModty = Const ModRel
  analyzableToken = AnTokenMultimode AnTokenModality --AnTokenSys $ AnTokenChainModty
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
        (AddressInfo ["underlying known modality"] FocusWrapped WorthMentioning)
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
        (\ d rel -> hoistcoy modedEqDeg $ Identity !<$> d)
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
        (AddressInfo ["trailing component"] NoFocus omit)
      return $ case token of
        TokenTrav -> AnalysisTrav $
          ChainModtyLink (getAnalysisTrav rkmu) (getAnalysisTrav rtermNu) (getAnalysisTrav rchainRho)
        TokenTC -> AnalysisTC $ _chainModty'dom chainRho :*: _knownModty'cod kmu
        TokenRel -> AnalysisRel

    ChainModtyTerm dom cod t -> Right $ do
      rdom <- fmapCoe runIdentity <$> h Identity
        (conditional $ ChainModtyTerm unreachable unreachable unreachable)
        (\ gamma' -> \ case
            (Classification (ChainModtyTerm dom' cod' t') U1 maybeDomCod') ->
              Just $ Identity !<$> Classification dom' U1 (ClassifWillBe U1)
            otherwise -> Nothing
        )
        extCtxId
        (\ d rel -> coy U1)
        (AddressInfo ["modality represented by a term: domain annotation"] FocusWrapped omit)
      rcod <- fmapCoe runIdentity <$> h Identity
        (conditional $ ChainModtyTerm unreachable unreachable unreachable)
        (\ gamma' -> \ case
            (Classification (ChainModtyTerm dom' cod' t') U1 maybeDomCod') ->
              Just $ Identity !<$> Classification cod' U1 (ClassifWillBe U1)
            otherwise -> Nothing
        )
        extCtxId
        (\ d rel -> coy U1)
        (AddressInfo ["modality represented by a term: codomain annotation"] FocusWrapped omit)
      rt <- fmapCoe runIdentity <$> h Identity
        (conditional $ ChainModtyTerm (getAnalysisTrav rdom) (getAnalysisTrav rcod) unreachable)
        (\ gamma' -> \ case
            (Classification (ChainModtyTerm dom' cod' t') U1 maybeDomCod') ->
              Just $ Identity !<$> Classification t' U1
                (ClassifMustBe $ BareSysType $ SysTypeModty dom' cod')
            otherwise -> Nothing
        )
        extCtxId
        (\ d rel -> hoistcoy modedEqDeg $ Identity !<$> d)
        (AddressInfo ["modality represented by a term: that underlying term"] FocusEliminee omit)
      return $ case token of
        TokenTrav -> AnalysisTrav $
          ChainModtyTerm (getAnalysisTrav rdom) (getAnalysisTrav rcod) (getAnalysisTrav rt)
        TokenTC -> AnalysisTC $ dom :*: cod
        TokenRel -> AnalysisRel

    ChainModtyMeta dom cod meta depcies -> Left $ AnErrorSys $ AnErrorChainModtyMeta
    
    ChainModtyAlreadyChecked dom cod chmu -> Left $ AnErrorSys $ AnErrorChainModtyAlreadyChecked
      
  convRel token d = U1 :*: U1
  extraClassif d t extraT = U1 :*: U1

instance Analyzable Reldtt KnownModty where
  type ClassifExtraInput KnownModty = U1
  type Classif KnownModty = ReldttMode :*: ReldttMode
  type Relation KnownModty = Const ModRel
  analyzableToken = AnTokenSys $ AnTokenKnownModty
  witClassif token = Witness
  --analyze token gamma (Classification kmu@(KnownModty snout tail) U1 maybeDomCod) h =
  --  Left $ AnErrorSys $ AnErrorKnownModty
  analyze token gamma (Classification kmu@(KnownModty snout tail) U1 maybeDomCod) h = Right $ do
    rsnout <- fmapCoe runIdentity <$> h Identity
      (conditional $ KnownModty snout unreachable)
      (\ gamma' (Classification kmu'@(KnownModty snout' tail') U1 maybeDomCod') ->
           Just $ Identity !<$> Classification (Const snout') U1 (ClassifWillBe U1)
      )
      extCtxId
      extRelId
      (AddressInfo ["snout of modality"] FocusWrapped omit)
    rtail <- fmapCoe runIdentity <$> h Identity
      (conditional $ KnownModty snout unreachable)
      (\ gamma' (Classification kmu'@(KnownModty snout' tail') U1 maybeDomCod') ->
           Just $ Identity !<$>
           Classification tail' (Const snout') (ClassifWillBe $ _modtyTail'dom tail' :*: _modtyTail'cod tail')
      )
      extCtxId
      extRelId
      (AddressInfo ["tail of modality"] FocusWrapped omit)
    return $ case token of
      TokenTrav -> AnalysisTrav $ KnownModty snout $ getAnalysisTrav rtail
      TokenTC -> AnalysisTC $ addIntToMode (_modtySnout'dom snout) domTail
                          :*: addIntToMode (_modtySnout'cod snout) codTail
        where domTail :*: codTail = getAnalysisTC rtail
      TokenRel -> AnalysisRel
  convRel token d = U1 :*: U1
  extraClassif d t extraT = U1 :*: U1

instance Analyzable Reldtt (Const ModtySnout) where
  type ClassifExtraInput (Const ModtySnout) = U1
  type Classif (Const ModtySnout) = U1
  type Relation (Const ModtySnout) = Const ModRel
  analyzableToken = AnTokenSys $ AnTokenModtySnout
  witClassif token = Witness
  analyze token gamma (Classification (Const snout) U1 maybeU1) h = Left $ AnErrorSys $ AnErrorModtySnout
  convRel token d = U1
  extraClassif d t extraT = U1

instance Analyzable Reldtt ModtyTail where
  type ClassifExtraInput ModtyTail = Const ModtySnout
  type Classif ModtyTail = ReldttMode :*: ReldttMode -- domain and codomain of the TAIL
  type Relation ModtyTail = Const ModRel
  analyzableToken = AnTokenSys $ AnTokenModtyTail
  witClassif token = Witness

  analyze token gamma (Classification tail (Const snout) maybeDomCod) h = case tail of

    TailEmpty -> Right $ do
      return $ case token of
        TokenTrav -> AnalysisTrav $ TailEmpty
        TokenTC -> AnalysisTC $ dzero :*: dzero
        TokenRel -> AnalysisRel

    TailDisc cod -> Right $ do
      rcod <- fmapCoe runIdentity <$> h Identity
        (conditional $ TailDisc unreachable)
        (\ gamma' (Classification tail' (Const snout') maybeDomCod') -> case tail' of
            TailDisc cod' ->
              Just $ Identity !<$> Classification cod' U1 (ClassifWillBe U1)
            otherwise -> Nothing
        )
        extCtxId
        (\ _ _ -> coy U1)
        (AddressInfo ["codomain"] FocusWrapped omit)
      return $ case token of
        TokenTrav -> AnalysisTrav $ TailDisc $ getAnalysisTrav rcod
        TokenTC -> AnalysisTC $ dzero :*: cod
        TokenRel -> AnalysisRel

    TailForget dom -> Right $ do
      rdom <- fmapCoe runIdentity <$> h Identity
        (conditional $ TailForget unreachable)
        (\ gamma' (Classification tail' (Const snout') maybeDomCod') -> case tail' of
            TailForget dom' ->
              Just $ Identity !<$> Classification dom' U1 (ClassifWillBe U1)
            otherwise -> Nothing
        )
        extCtxId
        (\ _ _ -> coy U1)
        (AddressInfo ["domain"] FocusWrapped omit)
      return $ case token of
        TokenTrav -> AnalysisTrav $ TailForget $ getAnalysisTrav rdom
        TokenTC -> AnalysisTC $ dom :*: dzero
        TokenRel -> AnalysisRel

    TailDiscForget dom cod -> Right $ do
      rdom <- fmapCoe runIdentity <$> h Identity
        (conditional $ TailDiscForget unreachable unreachable)
        (\ gamma' (Classification tail' (Const snout') maybeDomCod') -> case tail' of
            TailDiscForget dom' cod' ->
              Just $ Identity !<$> Classification dom' U1 (ClassifWillBe U1)
            otherwise -> Nothing
        )
        extCtxId
        (\ _ _ -> coy U1)
        (AddressInfo ["domain"] FocusWrapped omit)
      rcod <- fmapCoe runIdentity <$> h Identity
        (conditional $ TailDiscForget unreachable unreachable)
        (\ gamma' (Classification tail' (Const snout') maybeDomCod') -> case tail' of
            TailDiscForget dom' cod' ->
              Just $ Identity !<$> Classification cod' U1 (ClassifWillBe U1)
            otherwise -> Nothing
        )
        extCtxId
        (\ _ _ -> coy U1)
        (AddressInfo ["codomain"] FocusWrapped omit)
      return $ case token of
        TokenTrav -> AnalysisTrav $ TailDiscForget (getAnalysisTrav rdom) (getAnalysisTrav rcod)
        TokenTC -> AnalysisTC $ dom :*: cod
        TokenRel -> AnalysisRel

    TailCont d -> Right $ do
      rd <- fmapCoe runIdentity <$> h Identity
        (conditional $ TailCont unreachable)
        (\ gamma' (Classification tail' (Const snout') maybeDomCod') -> case tail' of
            TailCont d' ->
              Just $ Identity !<$> Classification d' U1 (ClassifWillBe U1)
            otherwise -> Nothing
        )
        extCtxId
        (\ _ _ -> coy U1)
        (AddressInfo ["mode"] FocusWrapped omit)
      return $ case token of
        TokenTrav -> AnalysisTrav $ TailForget $ getAnalysisTrav rd
        TokenTC -> AnalysisTC $ d :*: d
        TokenRel -> AnalysisRel

    TailProblem -> Right $ do
      return $ case token of
        TokenTrav -> AnalysisTrav $ TailEmpty
        TokenTC -> AnalysisTC $ dproblem :*: dproblem
        TokenRel -> AnalysisRel

    where dzero = ReldttMode $ BareMode $ ModeTermZero
          dproblem = ReldttMode $ Expr2 $ TermProblem $ Expr2 $ TermWildcard

  convRel token d = U1 :*: U1
  extraClassif d t extraT = U1 :*: U1

instance Analyzable Reldtt ReldttDegree where
  type ClassifExtraInput ReldttDegree = U1
  type Classif ReldttDegree = ReldttMode
  type Relation ReldttDegree = Const ModRel
  analyzableToken = AnTokenMultimode AnTokenDegree --AnTokenSys $ AnTokenReldttDegree
  witClassif token = Witness

  analyze token gamma (Classification deg U1 maybeD) h = case deg of

    DegKnown d kdeg -> Right $ do
      rd <- fmapCoe runIdentity <$> h Identity
        (conditional $ DegKnown unreachable kdeg)
        (\ gamma' -> \ case
            (Classification deg'@(DegKnown d' kdeg') U1 maybeD') ->
              Just $ Identity !<$> Classification d' U1 (ClassifWillBe U1)
            otherwise -> Nothing
        )
        extCtxId
        (\_ _ -> coy U1)
        (AddressInfo ["mode"] FocusWrapped omit)
      return $ case token of
        TokenTrav -> AnalysisTrav $ DegKnown (getAnalysisTrav rd) kdeg
        TokenTC -> AnalysisTC $ d
        TokenRel -> AnalysisRel

    DegGet degArg mu -> Right $ do
      rdegArg <- fmapCoe runIdentity <$> h Identity
        (conditional $ DegGet unreachable unreachable)
        (\ gamma' -> \ case
            (Classification deg'@(DegGet degArg' mu') U1 maybeD') ->
              Just $ Identity !<$> Classification degArg' U1 (ClassifMustBe $ _chainModty'cod mu')
            otherwise -> Nothing
        )
        extCtxId
        (\_ -> cutcoy $ \(Const modrel) -> Const modrel)
        (AddressInfo ["argument degree"] NoFocus omit)
      {-rdom <- fmapCoe runIdentity <$> h Identity
        (conditional $ DegGet (getAnalysisTrav rdegArg) unreachable unreachable unreachable)
        (\ gamma' -> \ case
            (Classification deg'@(DegGet degArg' mu' dom' cod') U1 maybeD') ->
              Just $ Identity !<$> Classification dom' U1 (ClassifWillBe U1)
            otherwise -> Nothing
        )
        extCtxId
        (\_ _ -> U1)
        (AddressInfo ["domain"] FocusWrapped omit)
      rcod <- fmapCoe runIdentity <$> h Identity
        (conditional $ DegGet (getAnalysisTrav rdegArg) unreachable unreachable unreachable)
        (\ gamma' -> \ case
            (Classification deg'@(DegGet degArg' mu' dom' cod') U1 maybeD') ->
              Just $ Identity !<$> Classification cod' U1 (ClassifWillBe U1)
            otherwise -> Nothing
        )
        extCtxId
        (\_ _ -> U1)
        (AddressInfo ["codomain"] FocusWrapped omit)-}
      rmu <- fmapCoe runIdentity <$> h Identity
        (conditional $ DegGet (getAnalysisTrav rdegArg) unreachable)
        (\ gamma' -> \ case
            (Classification deg'@(DegGet degArg' mu') U1 maybeD') ->
              Just $ Identity !<$> Classification mu' U1 ClassifUnknown --(ClassifMustBe $ dom' :*: cod')
            otherwise -> Nothing
        )
        extCtxId
        extRelId
        (AddressInfo ["modality"] FocusEliminee omit)
      return $ case token of
        TokenTrav -> AnalysisTrav $
          DegGet (getAnalysisTrav rdegArg) (getAnalysisTrav rmu) --(getAnalysisTrav rdom) (getAnalysisTrav rcod)
        TokenTC -> AnalysisTC $ _chainModty'dom mu
        TokenRel -> AnalysisRel

  convRel token d = U1
  extraClassif d t extraT = U1

instance Analyzable Reldtt ReldttSysTerm where
  type ClassifExtraInput ReldttSysTerm = ClassifExtraInput (Term Reldtt)
  type Classif ReldttSysTerm = Classif (Term Reldtt)
  type Relation ReldttSysTerm = Relation (Term Reldtt)
  analyzableToken = AnTokenSysTerm --AnTokenSys $ AnTokenReldttSysTerm
  witClassif token = Witness

  analyze token gamma (Classification syst U1 maybeTy) h = case syst of
    SysTermMode modeTerm -> Right $ do
      rmodeTerm <- fmapCoe runIdentity <$> h Identity
        (conditional $ SysTermMode unreachable)
        (\ gamma' -> \ case
            Classification syst'@(SysTermMode modeTerm') U1 maybeTy' ->
              Just $ Identity !<$> Classification modeTerm' U1 (ClassifWillBe U1)
            otherwise -> Nothing
        )
        extCtxId
        (\ d deg -> coy U1)
        (AddressInfo ["underlying mode term"] FocusWrapped EntirelyBoring)
      return $ case token of
        TokenTrav -> AnalysisTrav $ SysTermMode $ getAnalysisTrav rmodeTerm
        TokenTC -> AnalysisTC $ BareSysType $ SysTypeMode
        TokenRel -> AnalysisRel
    SysTermModty modtyTerm -> Right $ do
      rmodtyTerm <- fmapCoe runIdentity <$> h Identity
        (conditional $ SysTermModty unreachable)
        (\ gamma' -> \ case
            Classification syst'@(SysTermModty modtyTerm') U1 maybeTy' ->
              Just $ Identity !<$> Classification modtyTerm' U1
                (ClassifWillBe $ _modtyTerm'dom modtyTerm' :*: _modtyTerm'cod modtyTerm')
              {-(maybeTy' & \case
                  ClassifMustBe (BareSysType (SysTypeModty dom' cod')) -> ClassifWillBe (dom' :*: cod')
                  ClassifWillBe (BareSysType (SysTypeModty dom' cod')) -> ClassifWillBe (dom' :*: cod')
                  otherwise -> ClassifUnknown
              )-}
            otherwise -> Nothing
        )
        extCtxId
        (\ d deg -> coy U1)
        (AddressInfo ["underlying modality term"] FocusWrapped EntirelyBoring)
      return $ case token of 
        TokenTrav -> AnalysisTrav $ SysTermModty $ getAnalysisTrav rmodtyTerm
        TokenTC -> AnalysisTC $ BareSysType $ SysTypeModty dom cod
          where dom :*: cod = getAnalysisTC rmodtyTerm
        TokenRel -> AnalysisRel
    {-SysTermChainModtyInDisguise chmu -> Right $ do
      rchmu <- fmapCoe runIdentity <$> h Identity
        (conditional $ SysTermChainModtyInDisguise unreachable)
        (\ gamma' -> \ case
            Classification syst'@(SysTermChainModtyInDisguise chmu') U1 maybeTy' ->
              Just $ Identity !<$> Classification chmu' U1 ClassifUnknown
            otherwise -> Nothing
        )
        extCtxId
        (\ d deg -> Const ModEq)
        (AddressInfo ["underlying chain modality"] FocusWrapped omit)
      return $ case token of 
        TokenTrav -> AnalysisTrav $ SysTermChainModtyInDisguise $ getAnalysisTrav rchmu
        TokenTC -> AnalysisTC $ BareSysType $ SysTypeModty dom cod
          where dom :*: cod = getAnalysisTC rchmu
        TokenRel -> AnalysisRel-}

  convRel token d = modedEqDeg $ uncoy d
  extraClassif d t extraT = U1

instance Analyzable Reldtt ModeTerm where
  type ClassifExtraInput ModeTerm = U1
  type Classif ModeTerm = U1
  type Relation ModeTerm = U1
  analyzableToken = AnTokenSys $ AnTokenModeTerm
  witClassif token = Witness

  analyze token gamma (Classification modeTerm U1 maybeU1) h = case modeTerm of
    ModeTermZero -> Right $ do
      return $ case token of
        TokenTrav -> AnalysisTrav $ ModeTermZero
        TokenTC -> AnalysisTC $ U1
        TokenRel -> AnalysisRel
    ModeTermSuc t -> Right $ do
      rt <- fmapCoe runIdentity <$> h Identity
        (conditional $ ModeTermSuc unreachable)
        (\ gamma' -> \ case
            Classification modeTerm'@(ModeTermSuc t') U1 maybeU1' ->
              Just $ Identity !<$> Classification t' U1 (ClassifMustBe $ BareSysType $ SysTypeMode)
            otherwise -> Nothing
        )
        extCtxId
        (\ d _ -> Identity !<$> hoistcoy modedEqDeg d)
        (AddressInfo ["predecessor mode"] FocusWrapped omit)
      return $ case token of
        TokenTrav -> AnalysisTrav $ ModeTermSuc $ getAnalysisTrav rt
        TokenTC -> AnalysisTC $ U1
        TokenRel -> AnalysisRel
    ModeTermOmega -> Right $ do
      return $ case token of
        TokenTrav -> AnalysisTrav $ ModeTermOmega
        TokenTC -> AnalysisTC $ U1
        TokenRel -> AnalysisRel

  convRel token d = U1
  extraClassif d t extraT = U1

instance Analyzable Reldtt ModtyTerm where
  type ClassifExtraInput ModtyTerm = U1
  type Classif ModtyTerm = ReldttMode :*: ReldttMode
  type Relation ModtyTerm = U1
  analyzableToken = AnTokenSys $ AnTokenModtyTerm
  witClassif token = Witness

  analyze token gamma (Classification modtyTerm U1 maybeDomCod) h = case modtyTerm of
    ModtyTermChain chmu -> Right $ do
      rchmu <- fmapCoe runIdentity <$> h Identity
        (conditional $ ModtyTermChain unreachable)
        (\ gamma' -> \ case
            Classification modtyTerm'@(ModtyTermChain chmu') U1 maybeDomCod' ->
              Just $ Identity !<$> Classification chmu' U1 (classifMust2will maybeDomCod')
            otherwise -> Nothing
        )
        extCtxId
        (\ d _ -> coy $ Const ModEq)
        (AddressInfo ["underlying chain modality"] FocusWrapped WorthMentioning)
      return $ case token of 
        TokenTrav -> AnalysisTrav $ ModtyTermChain $ getAnalysisTrav rchmu
        TokenTC -> AnalysisTC $ dom :*: cod
          where dom :*: cod = getAnalysisTC rchmu
        TokenRel -> AnalysisRel
    ModtyTermDiv rho mu -> unreachable -- only for prettyprinting
    ModtyTermApproxLeftAdjointProj muArg -> Right $ do
      {-rdomResult <- fmapCoe runIdentity <$> h Identity
        (conditional $ ModtyTermApproxLeftAdjointProj unreachable unreachable unreachable)
        (\ gamma' -> \ case
            (Classification modtyTerm'@(ModtyTermApproxLeftAdjointProj domResult' codResult' muArg') U1 maybeDomCod) ->
              Just $ Identity !<$> Classification domResult' U1 (ClassifWillBe U1)
            otherwise -> Nothing
        )
        extCtxId
        (\_ U1 -> U1)
        (AddressInfo ["domain of result"] NoFocus omit)
      rcodResult <- fmapCoe runIdentity <$> h Identity
        (conditional $ ModtyTermApproxLeftAdjointProj unreachable unreachable unreachable)
        (\ gamma' -> \ case
            (Classification modtyTerm'@(ModtyTermApproxLeftAdjointProj domResult' codResult' muArg') U1 maybeDomCod) ->
              Just $ Identity !<$> Classification codResult' U1 (ClassifWillBe U1)
            otherwise -> Nothing
        )
        extCtxId
        (\_ U1 -> U1)
        (AddressInfo ["codomain of result"] NoFocus omit)-}
      rmuArg <- fmapCoe runIdentity <$> h Identity
        (conditional $ ModtyTermApproxLeftAdjointProj unreachable)
        (\ gamma' -> \ case
            (Classification modtyTerm'@(ModtyTermApproxLeftAdjointProj muArg') U1 maybeDomCod) ->
              Just $ Identity !<$>
                Classification muArg' U1 (ClassifWillBe $ _chainModty'dom muArg' :*: _chainModty'cod muArg')
            otherwise -> Nothing
        )
        extCtxId
        (\d _ -> coy $ Const ModEq)
        (AddressInfo ["argument modality"] FocusEliminee omit)
      return $ case token of
        TokenTrav -> AnalysisTrav $
          ModtyTermApproxLeftAdjointProj (getAnalysisTrav rmuArg)
        TokenTC -> AnalysisTC $ _chainModty'cod muArg :*: _chainModty'dom muArg -- purposefully swapped
        TokenRel -> AnalysisRel
    ModtyTermComp mu2 mu1 -> Right $ do
      {-rdom <- fmapCoe runIdentity <$> h Identity
        (conditional $ ModtyTermComp unreachable unreachable unreachable unreachable unreachable)
        (\ gamma' -> \ case
            (Classification modtyTerm'@(ModtyTermComp cod' mu2' mid' mu1' dom') U1 maybeDomCod) ->
              Just $ Identity !<$> Classification dom' U1 (ClassifWillBe U1)
            otherwise -> Nothing
        )
        extCtxId
        (\_ U1 -> U1)
        (AddressInfo ["domain"] NoFocus omit)
      rmid <- fmapCoe runIdentity <$> h Identity
        (conditional $ ModtyTermComp unreachable unreachable unreachable unreachable unreachable)
        (\ gamma' -> \ case
            (Classification modtyTerm'@(ModtyTermComp cod' mu2' mid' mu1' dom') U1 maybeDomCod) ->
              Just $ Identity !<$> Classification mid' U1 (ClassifWillBe U1)
            otherwise -> Nothing
        )
        extCtxId
        (\_ U1 -> U1)
        (AddressInfo ["intermediate mode"] NoFocus omit)
      rcod <- fmapCoe runIdentity <$> h Identity
        (conditional $ ModtyTermComp unreachable unreachable unreachable unreachable unreachable)
        (\ gamma' -> \ case
            (Classification modtyTerm'@(ModtyTermComp cod' mu2' mid' mu1' dom') U1 maybeDomCod) ->
              Just $ Identity !<$> Classification cod' U1 (ClassifWillBe U1)
            otherwise -> Nothing
        )
        extCtxId
        (\_ U1 -> U1)
        (AddressInfo ["codomain"] NoFocus omit)-}
      rmu1 <- fmapCoe runIdentity <$> h Identity
        --(conditional $ ModtyTermComp (getAnalysisTrav rcod)
        --                 unreachable (getAnalysisTrav rmid)
        --                 unreachable (getAnalysisTrav rdom))
        (conditional $ ModtyTermComp unreachable unreachable)
        (\ gamma' -> \ case
            (Classification modtyTerm'@(ModtyTermComp mu2' mu1') U1 maybeDomCod) ->
              Just $ Identity !<$> Classification mu1' U1 ClassifUnknown
            otherwise -> Nothing
        )
        extCtxId
        (\_ _ -> coy $ Const ModEq)
        (AddressInfo ["precomposite"] FocusEliminee omit)
      rmu2 <- fmapCoe runIdentity <$> h Identity
        --(conditional $ ModtyTermComp (getAnalysisTrav rcod)
        --                 unreachable (getAnalysisTrav rmid)
        --                 unreachable (getAnalysisTrav rdom))
        (conditional $ ModtyTermComp unreachable unreachable)
        (\ gamma' -> \ case
            (Classification modtyTerm'@(ModtyTermComp mu2' mu1') U1 maybeDomCod) ->
              Just $ Identity !<$> Classification mu2' U1 (ClassifMustBe $ _chainModty'cod mu1' :*: _chainModty'cod mu2')
            otherwise -> Nothing
        )
        extCtxId
        (\_ _ -> coy $ Const ModEq)
        (AddressInfo ["postcomposite"] FocusEliminee omit)
      return $ case token of
        --TokenTrav -> AnalysisTrav $ ModtyTermComp (getAnalysisTrav rcod)
        --                   (getAnalysisTrav rmu2) (getAnalysisTrav rmid)
        --                   (getAnalysisTrav rmu1) (getAnalysisTrav rdom)
        TokenTrav -> AnalysisTrav $ ModtyTermComp (getAnalysisTrav rmu2) (getAnalysisTrav rmu1)
        TokenTC -> AnalysisTC $ _chainModty'dom mu1 :*: _chainModty'cod mu2
        TokenRel -> AnalysisRel
    ModtyTermUnavailable dom cod -> unreachable -- only for prettyprinting

  convRel token d = U1 :*: U1
  extraClassif d t extraT = U1 :*: U1

instance Analyzable Reldtt ReldttUniHSConstructor where
  type ClassifExtraInput ReldttUniHSConstructor = ClassifExtraInput (UniHSConstructor Reldtt)
  type Classif ReldttUniHSConstructor = Classif (UniHSConstructor Reldtt)
  type Relation ReldttUniHSConstructor = Relation (UniHSConstructor Reldtt)
  analyzableToken = AnTokenSysUniHSConstructor --AnTokenSys $ AnTokenReldttUniHSConstructor
  witClassif token = Witness

  analyze token gamma (Classification ty U1 maybeD) h = case ty of
    SysTypeMode -> Right $ do
      return $ case token of
        TokenTrav -> AnalysisTrav $ SysTypeMode
        TokenTC -> AnalysisTC $ ModalBox $ Const1 $ ReldttMode $ BareMode $ ModeTermZero
        TokenRel -> AnalysisRel
    SysTypeModty dom cod -> Right $ do
      rdom <- fmapCoe runIdentity <$> h Identity
        (conditional $ SysTypeModty unreachable unreachable)
        (\ gamma' -> \ case
            (Classification ty'@(SysTypeModty dom' cod') U1 maybeD') ->
              Just $ Identity !<$> Classification dom' U1 (ClassifWillBe U1)
            otherwise -> Nothing
        )
        extCtxId
        (\d deg -> coy U1)
        (AddressInfo ["domain"] FocusWrapped omit)
      rcod <- fmapCoe runIdentity <$> h Identity
        (conditional $ SysTypeModty unreachable unreachable)
        (\ gamma' -> \ case
            (Classification ty'@(SysTypeModty dom' cod') U1 maybeD') ->
              Just $ Identity !<$> Classification cod' U1 (ClassifWillBe U1)
            otherwise -> Nothing
        )
        extCtxId
        (\d deg -> coy U1)
        (AddressInfo ["codomain"] FocusWrapped omit)
      return $ case token of
        TokenTrav -> AnalysisTrav $ SysTypeModty (getAnalysisTrav rdom) (getAnalysisTrav rcod)
        TokenTC -> AnalysisTC $ ModalBox $ Const1 $ ReldttMode $ BareMode $ ModeTermZero
        TokenRel -> AnalysisRel
    {-SysTypeChainModtyDisguisedAsTerm dom cod -> Right $ do
      rdom <- fmapCoe runIdentity <$> h Identity
        (conditional $ SysTypeChainModtyDisguisedAsTerm unreachable unreachable)
        (\ gamma' -> \ case
            (Classification ty'@(SysTypeChainModtyDisguisedAsTerm dom' cod') U1 maybeD') ->
              Just $ Identity !<$> Classification dom' U1 (ClassifWillBe U1)
            otherwise -> Nothing
        )
        extCtxId
        (\d deg -> U1)
        (AddressInfo ["domain"] FocusWrapped omit)
      rcod <- fmapCoe runIdentity <$> h Identity
        (conditional $ SysTypeChainModtyDisguisedAsTerm unreachable unreachable)
        (\ gamma' -> \ case
            (Classification ty'@(SysTypeChainModtyDisguisedAsTerm dom' cod') U1 maybeD') ->
              Just $ Identity !<$> Classification cod' U1 (ClassifWillBe U1)
            otherwise -> Nothing
        )
        extCtxId
        (\d deg -> U1)
        (AddressInfo ["codomain"] FocusWrapped omit)
      return $ case token of
        TokenTrav -> AnalysisTrav $ SysTypeChainModtyDisguisedAsTerm (getAnalysisTrav rdom) (getAnalysisTrav rcod)
        TokenTC -> AnalysisTC $ ReldttMode $ BareMode $ ModeTermZero
        TokenRel -> AnalysisRel-}

  convRel token d = U1
  extraClassif d t extraT = crispModalityTo (uncoy d) :*: U1

--------------------------------

instance SysAnalyzer Reldtt where
  quickEqSysUnanalyzable sysError sysToken t1 t2 extraT1 extraT2 = case (sysError, sysToken) of
    (AnErrorModtySnout, AnTokenSys AnTokenModtySnout) ->
      let Const snout1 = t1
          Const snout2 = t2
      in  snout1 == snout2
    (AnErrorModtySnout, _) -> unreachable
    (AnErrorChainModtyMeta, AnTokenMultimode AnTokenModality) -> case (t1, t2) of
      (ChainModtyMeta dom1 cod1 meta1 (Compose depcies1), ChainModtyMeta dom2 cod2 meta2 (Compose depcies2)) ->
        meta1 == meta2
        && length depcies1 == length depcies2
        && and (zip depcies1 depcies2 <&> \ (d1 :*: depcy1, d2 :*: depcy2) ->
                   quickEq @Reldtt depcy1 depcy2 U1 U1
               )
      (ChainModtyMeta _ _ _ _, _) -> False
      (_, ChainModtyMeta _ _ _ _) -> False
      otherwise -> unreachable
    (AnErrorChainModtyMeta, _) -> unreachable
    (AnErrorChainModtyAlreadyChecked, AnTokenMultimode AnTokenModality) -> case (t1, t2) of
      (ChainModtyAlreadyChecked _ _ chmu1, ChainModtyAlreadyChecked _ _ chmu2) -> quickEq @Reldtt chmu1 chmu2 U1 U1
      otherwise -> False
    (AnErrorChainModtyAlreadyChecked, _) -> unreachable
    {-(AnErrorKnownModty, AnTokenKnownModty) -> case (t1, t2) of
      (KnownModty snout1 tail1, KnownModty snout2 tail2) ->
        (snout1 == snout2) && case (tail1, tail2) of
          (TailEmpty, TailEmpty) -> True
          (TailDisc cod1, TailDisc cod2) -> quickEq cod1 cod2 U1 U1
          --()
    -}
--------------------------------

instance Solvable Reldtt ChainModty where
  astAlreadyChecked chmu (dom :*: cod) = ChainModtyAlreadyChecked dom cod chmu
  unMeta (ChainModtyMeta dom cod meta (Compose depcies)) = Just (MetaBlocked, meta, depcies)
  unMeta _ = Nothing
