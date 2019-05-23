{-# LANGUAGE UndecidableInstances #-}

module Menkar.Analyzer.Syntax where

import Menkar.Analyzer.Class
import Menkar.System.Analyzer
import Menkar.Fine.Syntax
import Menkar.Fine.Context
import Menkar.System.Fine.Multimode

import Data.Functor.Functor1
import Data.Omissible
import Control.Exception.AssertFalse
import Data.Constraint.Witness
import Data.Constraint.Conditional
import Data.Functor.Coerce

import GHC.Generics
import Data.Functor.Const
import Control.Lens
import Data.Functor.Compose
import Control.Monad
import Data.Void
import Data.Maybe
import Data.List

fromRight :: b -> Either a b -> b
fromRight b0 (Left a) = b0
fromRight b0 (Right b) = b

-------------------------

instance (SysAnalyzer sys) => Analyzable sys (ModedModality sys) where
  type Classif (ModedModality sys) = Mode sys :*: Mode sys -- domain and codomain
  type Relation (ModedModality sys) = Const ModRel
  type ClassifExtraInput (ModedModality sys) = U1
  analyzableToken = AnTokenModedModality
  witClassif token = Witness
  analyze token gamma (Classification (ModedModality dom cod mu) U1 _) h = Right $ do
    rdom <- h Identity
      _
      (\ gamma' (Classification (ModedModality dom' cod' mu') U1 _) ->
         Just $ Identity !<$> Classification dom' U1 (ClassifWillBe U1))
      extCtxId
      (const U1)
      (AddressInfo ["domain"] True omit)
    rcod <- h Identity
      _
      (\ gamma' (Classification (ModedModality dom' cod' mu') U1 _) ->
         Just $ Identity !<$> Classification cod' U1 (ClassifWillBe U1))
      extCtxId
      (const U1)
      (AddressInfo ["codomain"] True omit)
    rmu <- h Identity
      _
      (\ gamma' (Classification (ModedModality dom' cod' mu') U1 _) ->
         Just $ Identity !<$> Classification mu' U1 (ClassifWillBe $ dom' :*: cod'))
      extCtxId
      (fmapCoe Identity)
      (AddressInfo ["modality"] True omit)
    return $ case token of
        TokenTrav ->
          AnalysisTrav $ runIdentity !<$> ModedModality (getAnalysisTrav rdom) (getAnalysisTrav rcod) (getAnalysisTrav rmu)
        TokenTC -> AnalysisTC $ dom :*: cod
        TokenRel -> AnalysisRel
  convRel token d = U1 :*: U1
  extraClassif = U1 :*: U1

-------------------------

instance (SysAnalyzer sys,
          Analyzable sys (rhs sys),
          Relation (rhs sys) ~ ModedDegree sys,
          ClassifExtraInput (rhs sys) ~ U1,
          ClassifExtraInput (Classif (rhs sys)) ~ U1
         ) => Analyzable sys (Binding Type rhs sys) where
  type Classif (Binding Type rhs sys) = Classif (Segment Type sys) :*: ClassifBinding Type (Classif (rhs sys)) sys
  type Relation (Binding Type rhs sys) = ModedDegree sys
  type ClassifExtraInput (Binding Type rhs sys) = U1
  analyzableToken = AnTokenBinding analyzableToken
  witClassif token = haveClassif @sys @(rhs sys) Witness
  analyze token gamma (Classification (Binding seg body) U1 maybeCl) h = Right $ do
    rseg <- h Identity
      _
      (\ gamma' (Classification (Binding seg' body') U1 maybeCl') ->
         Just $ Identity !<$> Classification seg' U1 (fst1 <$> classifMust2will maybeCl'))
      extCtxId
      (fmapCoe Identity)
      (AddressInfo ["segment"] False omit)
    rbody <- h VarWkn
      _
      (\ gamma' (Classification (Binding seg' body') U1 maybeCl') ->
         Just $ Classification body' U1 (_classifBinding'body . snd1 <$> classifMust2will maybeCl'))
      (\ token' gamma' (Classification (Binding seg1 body1) U1 maybeCl1) condInput2 ->
         Just $ gamma' :..
           (decl'content %~ \ ty1 ->
             toTypeMaybeTwice token' ty1 $
             fmap VarFromCtx . _decl'content . binding'segment . _classification'get <$> condInput2
           )
           (VarFromCtx <$> seg1)
      )
      (fmap VarWkn)
      (AddressInfo ["body"] False omit)
    return $ case token of
      TokenTrav -> AnalysisTrav $ Binding (runIdentity !<$> getAnalysisTrav rseg) (getAnalysisTrav rbody)
      TokenTC -> AnalysisTC $
        (runIdentity !<$> getAnalysisTC rseg) :*: ClassifBinding seg (getAnalysisTC rbody)
      TokenRel -> AnalysisRel
  convRel token d = U1 :*: Comp1 (convRel (analyzableToken @sys @(rhs sys)) (VarWkn <$> d))
  extraClassif = U1 :*: Comp1 (extraClassif @sys @(rhs sys))

-------------------------

instance (SysAnalyzer sys,
          Analyzable sys rhs
          --Relation rhs ~ ModedDegree sys,
          --ClassifExtraInput rhs ~ U1
         ) => Analyzable sys (ClassifBinding Type rhs sys) where
  type Classif (ClassifBinding Type rhs sys) = ClassifBinding Type (Classif rhs) sys
  type Relation (ClassifBinding Type rhs sys) = Relation rhs :.: VarExt
  type ClassifExtraInput (ClassifBinding Type rhs sys) = ClassifExtraInput rhs :.: VarExt
  analyzableToken = AnTokenClassifBinding analyzableToken
  witClassif token = haveClassif @sys @rhs Witness
  analyze token gamma
    (Classification (ClassifBinding seg body) (Comp1 extraBody) maybeCl) h = Right $ do
    rbody <- h VarWkn
      _
      (\ gamma' (Classification (ClassifBinding seg' body') (Comp1 extraBody') maybeCl') ->
         Just $ Classification body' extraBody' (_classifBinding'body <$> classifMust2will maybeCl'))
      (\ token' gamma' (Classification (ClassifBinding seg1 body1) (Comp1 extraBody1) maybeCl1) condInput2 ->
         Just $ gamma' :..
           (decl'content %~ \ ty1 ->
             toTypeMaybeTwice token' ty1 $
             fmap VarFromCtx . _decl'content . _classifBinding'segment . _classification'get <$>
             condInput2
           )
           (VarFromCtx <$> seg1)
      )
      unComp1
      (AddressInfo ["body"] False EntirelyBoring)
    return $ case token of
      TokenTrav -> AnalysisTrav $ ClassifBinding _seg (getAnalysisTrav rbody)
      TokenTC -> AnalysisTC $ ClassifBinding seg (getAnalysisTC rbody)
      TokenRel -> AnalysisRel
  convRel token d = Comp1 $ convRel (analyzableToken @sys @rhs) (VarWkn <$> d)
  extraClassif = Comp1 $ extraClassif @sys @rhs

-------------------------

instance (SysAnalyzer sys,
          Analyzable sys (rhs sys)
         ) => Analyzable sys (NamedBinding rhs sys) where
  type Classif (NamedBinding rhs sys) = ClassifBinding Type (Classif (rhs sys)) sys
  type Relation (NamedBinding rhs sys) = Relation (rhs sys) :.: VarExt
  type ClassifExtraInput (NamedBinding rhs sys) =
    Segment Type sys :*: (ClassifExtraInput (rhs sys) :.: VarExt)
  analyzableToken = AnTokenNamedBinding analyzableToken
  witClassif token = haveClassif @sys @(rhs sys) Witness
  analyze token gamma
    (Classification (NamedBinding name body) (seg :*: Comp1 extraBody) maybeCl) h = Right $ do
    rbody <- h VarWkn
      _
      (\ gamma' (Classification (NamedBinding name' body') (seg' :*: Comp1 extraBody') maybeCl') ->
         Just $ Classification body' extraBody' (_classifBinding'body <$> classifMust2will maybeCl'))
      (\ token' gamma'
         (Classification (NamedBinding name1 body1) (seg1 :*: Comp1 extraBody1) maybeCl1)
         condInput2 ->
         Just $ gamma' :.. VarFromCtx <$> (Declaration
           (DeclNameSegment name1)
           (_decl'modty seg1)
           (_decl'plicity seg1)
           (toTypeMaybeTwice token'
             (_decl'content seg1)
             (_decl'content . fst1 . _classification'extra <$> condInput2)
           )
         )
      )
      unComp1
      (AddressInfo ["body"] False EntirelyBoring)
    return $ case token of
      TokenTrav -> AnalysisTrav $ NamedBinding name $ getAnalysisTrav rbody
      TokenTC -> AnalysisTC $
        ClassifBinding ((decl'name .~ DeclNameSegment name) seg) (getAnalysisTC rbody)
      TokenRel -> AnalysisRel
  convRel token d = Comp1 $ convRel (analyzableToken @sys @(rhs sys)) (VarWkn <$> d)
  extraClassif = Comp1 $ extraClassif @sys @(rhs sys)

-------------------------

instance (SysAnalyzer sys) => Analyzable sys (UniHSConstructor sys) where
  
  type Classif (UniHSConstructor sys) = Mode sys
  type Relation (UniHSConstructor sys) = ModedDegree sys
  type ClassifExtraInput (UniHSConstructor sys) = U1
  analyzableToken = AnTokenUniHSConstructor
  witClassif token = Witness
  analyze (token :: AnalyzerToken option) gamma
    (Classification (ty :: UniHSConstructor sys v) U1 maybeD) h = Right $ do
    
    let dgamma' = ctx'mode gamma
    let dgamma = unVarFromCtx <$> dgamma'

    case ty of

      UniHS d -> do
        rd <- h Identity
          _
          (\ gamma' -> \ case
              (Classification (UniHS d') U1 maybeD') ->
                Just $ Identity !<$> Classification d' U1 (ClassifWillBe U1)
              otherwise -> Nothing
          )
          extCtxId
          (const U1)
          (AddressInfo ["mode"] False omit)
        return $ case token of
          TokenTrav -> AnalysisTrav $ runIdentity !<$> UniHS (getAnalysisTrav rd)
          TokenTC -> AnalysisTC $ d
          TokenRel -> AnalysisRel

      Pi binding -> handleBinder Pi binding $ \case
        Pi binding -> Just binding
        _ -> Nothing

      Sigma binding -> handleBinder Sigma binding $ \case
        Sigma binding -> Just binding
        _ -> Nothing

      EmptyType -> handleConstant

      UnitType -> handleConstant

      BoxType segment -> do
        let extract (BoxType segment) = Just segment
            extract _ = Nothing
        rsegment <- h Identity
              _
              (\ gamma' (Classification ty' U1 maybeD') -> extract ty' <&> \ segment' ->
                  Identity !<$> Classification segment' U1 (ClassifWillBe $ U1))
              extCtxId
              (fmapCoe Identity)
              (AddressInfo ["segment"] False EntirelyBoring)
        return $ case token of
          TokenTrav -> AnalysisTrav $ BoxType $ runIdentity !<$> getAnalysisTrav rsegment
          TokenTC -> AnalysisTC $ dgamma
          TokenRel -> AnalysisRel

      NatType -> handleConstant

      EqType tyAmbient tL tR -> do
        rtyAmbient <- h Identity
          _
          (\ gamma' -> \ case
              Classification (EqType tyAmbient' tL' tR') U1 maybeD' ->
                Just $ Identity !<$> Classification tyAmbient' U1 (ClassifWillBe U1)
              otherwise -> Nothing
          )
          extCtxId
          (fmapCoe Identity)
          (AddressInfo ["ambient type"] False omit)
        rtL <- h Identity
          _
          (\ gamma' -> \ case
              Classification (EqType tyAmbient' tL' tR') U1 maybeD' ->
                Just $ Identity !<$> Classification tL' U1 (ClassifMustBe tyAmbient')
              otherwise -> Nothing
          )
          extCtxId
          (fmapCoe Identity)
          (AddressInfo ["left equand"] False omit)
        rtR <- h Identity
          _
          (\ gamma' -> \ case
              Classification (EqType tyAmbient' tL' tR') U1 maybeD' ->
                Just $ Identity !<$> Classification tR' U1 (ClassifMustBe tyAmbient')
              otherwise -> Nothing
          )
          extCtxId
          (fmapCoe Identity)
          (AddressInfo ["right equand"] False omit)
        return $ case token of
          TokenTrav ->
            AnalysisTrav $ runIdentity !<$> EqType (getAnalysisTrav rtyAmbient) (getAnalysisTrav rtL) (getAnalysisTrav rtR)
          TokenTC -> AnalysisTC $ dgamma
          TokenRel -> AnalysisRel

      SysType systy -> do
        rsysty <- h Identity
          _
          (\ gamma' -> \ case
              Classification (SysType systy') U1 maybeD' ->
                Just $ Identity !<$> Classification systy' U1 (classifMust2will maybeD')
              otherwise -> Nothing
          )
          extCtxId
          (fmapCoe Identity)
          (AddressInfo ["system-specific type"] False EntirelyBoring)
        return $ case token of
          TokenTrav -> AnalysisTrav $ SysType $ runIdentity !<$> getAnalysisTrav rsysty
          TokenTC -> AnalysisTC $ runIdentity !<$> getAnalysisTC rsysty
          TokenRel -> AnalysisRel
        
    where handleBinder ::
            (forall w . Binding Type Type sys w -> UniHSConstructor sys w) ->
            Binding Type Type sys v ->
            (forall w . UniHSConstructor sys w -> Maybe (Binding Type Type sys w)) ->
            _ (Analysis option (UniHSConstructor sys) vOut {-v-})
          handleBinder binder binding extract = do
            rbinding <- h Identity
              _
              (\ gamma' (Classification ty' U1 maybeD') -> extract ty' <&> \ binding' ->
                  Identity !<$> Classification binding' U1
                    (ClassifWillBe $ U1 :*: ClassifBinding (binding'segment binding') U1)
              )
              extCtxId
              (fmapCoe Identity)
              (AddressInfo ["binding"] False EntirelyBoring)
            return $ case token of
              TokenTrav -> AnalysisTrav $ binder $ runIdentity !<$> getAnalysisTrav rbinding
              TokenTC -> AnalysisTC $ unVarFromCtx <$> ctx'mode gamma
              TokenRel -> AnalysisRel
              
          handleConstant = pure $ case token of
            TokenTrav -> AnalysisTrav $ ty
            TokenTC -> AnalysisTC $ unVarFromCtx <$> ctx'mode gamma
            TokenRel -> AnalysisRel
            
  convRel token d = U1
  extraClassif = U1

-------------------------

instance SysAnalyzer sys => Analyzable sys (ConstructorTerm sys) where
  type Classif (ConstructorTerm sys) = Type sys
  type Relation (ConstructorTerm sys) = ModedDegree sys
  type ClassifExtraInput (ConstructorTerm sys) = U1
  analyzableToken = AnTokenConstructorTerm
  witClassif token = Witness
  analyze token gamma (Classification t U1 _) h = Right $ do
    
    let dgamma' = ctx'mode gamma
    let dgamma = unVarFromCtx <$> dgamma'

    case t of

      ConsUniHS ty -> do
        rty <- h Identity
          _
          (\ gamma' -> \ case
              Classification (ConsUniHS ty') U1 _ ->
                Just $ Identity !<$> Classification ty' U1 ClassifUnknown
              otherwise -> Nothing
          )
          extCtxId
          (fmapCoe Identity)
          (AddressInfo ["UniHS-constructor"] False EntirelyBoring)
        return $ case token of
          TokenTrav -> AnalysisTrav $ ConsUniHS $ runIdentity !<$> getAnalysisTrav rty
          TokenTC -> AnalysisTC $ hs2type $ UniHS $ runIdentity !<$> getAnalysisTC rty
          TokenRel -> AnalysisRel

      Lam binding -> do
        rbinding <- h Identity
          _
          (\ gamma' -> \ case
              Classification (Lam binding') U1 _ ->
                Just $ Identity !<$> Classification binding' U1 ClassifUnknown
              otherwise -> Nothing
          )
          extCtxId
          (fmapCoe Identity)
          (AddressInfo ["binding"] False EntirelyBoring)
        return $ case token of
          TokenTrav -> AnalysisTrav $ Lam $ runIdentity !<$> getAnalysisTrav rbinding
          TokenTC -> AnalysisTC $ hs2type $ Pi $ Binding (binding'segment binding) $
            _classifBinding'body $ snd1 $ runIdentity !<$> getAnalysisTC rbinding
            --let (U1 :*: Comp1 ty) = getAnalysisTC rbinding
            --in  AnalysisTC $ hs2type $ Pi $ Binding (binding'segment binding) ty
          TokenRel -> AnalysisRel

      Pair sigmaBinding tFst tSnd -> do
        rsigmaBinding <- h Identity
          _
          (\ gamma' -> \ case
              Classification (Pair sigmaBinding' tFst' tSnd') U1 _ ->
                Just $ Identity !<$> Classification sigmaBinding' U1
                  (ClassifWillBe $ U1 :*: ClassifBinding (binding'segment sigmaBinding') U1)
              otherwise -> Nothing
          )
          extCtxId
          (fmapCoe Identity)
          (AddressInfo ["Sigma-type annotation"] False omit)
        rtFst <- h Identity
          _
          (\ gamma' -> \ case
              Classification (Pair sigmaBinding' tFst' tSnd') U1 _ ->
                Just $ Identity !<$> Classification tFst' U1
                  (ClassifMustBe $ _segment'content $ binding'segment $ sigmaBinding')
              otherwise -> Nothing
          )
          extCtxId
          (fmapCoe Identity)
          (AddressInfo ["first component"] False omit)
        rtSnd <- h Identity
          _
          (\ gamma' -> \ case
              Classification (Pair sigmaBinding' tFst' tSnd') U1 _ ->
                Just $ Identity !<$> Classification tSnd' U1
                  (ClassifMustBe $ substLast2 tFst' $ binding'body sigmaBinding')
              otherwise -> Nothing
          )
          extCtxId
          (fmapCoe Identity)
          (AddressInfo ["second component"] False omit)
        return $ case token of
          TokenTrav ->
            AnalysisTrav $ runIdentity !<$> Pair (getAnalysisTrav rsigmaBinding) (getAnalysisTrav rtFst) (getAnalysisTrav rtSnd)
          TokenTC -> AnalysisTC $ hs2type $ Sigma sigmaBinding
          TokenRel -> AnalysisRel

      ConsUnit -> pure $ case token of
        TokenTrav -> AnalysisTrav $ ConsUnit
        TokenTC -> AnalysisTC $ hs2type $ UnitType
        TokenRel -> AnalysisRel

      ConsBox boxSeg tUnbox -> do
        rboxSeg <- h Identity
          _
          (\ gamma' -> \ case
              Classification (ConsBox boxSeg' tUnbox') U1 _ ->
                Just $ Identity !<$> Classification boxSeg' U1 (ClassifWillBe $ U1)
              otherwise -> Nothing
          )
          extCtxId
          (fmapCoe Identity)
          (AddressInfo ["Box-type annotation"] False omit)
        rtUnbox <- h Identity
          _
          (\ gamma' -> \ case
              Classification (ConsBox boxSeg' tUnbox') U1 _ ->
                Just $ Identity !<$> Classification tUnbox' U1
                  (ClassifMustBe $ _segment'content boxSeg')
              otherwise -> Nothing
          )
          extCtxId
          (fmapCoe Identity)
          (AddressInfo ["box content"] False omit)
        return $ case token of
          TokenTrav -> AnalysisTrav $ runIdentity !<$> ConsBox (getAnalysisTrav rboxSeg) (getAnalysisTrav rtUnbox)
          TokenTC -> AnalysisTC $ hs2type $ BoxType boxSeg
          TokenRel -> AnalysisRel

      ConsZero -> pure $ case token of
        TokenTrav -> AnalysisTrav $ ConsZero
        TokenTC -> AnalysisTC $ hs2type $ NatType
        TokenRel -> AnalysisRel

      ConsSuc t -> do
        rt <- h Identity
          _
          (\ gamma' -> \ case
              Classification (ConsSuc t') U1 _ ->
                Just $ Identity !<$> Classification t' U1 (ClassifMustBe $ hs2type NatType)
              otherwise -> Nothing
          )
          extCtxId
          (fmapCoe Identity)
          (AddressInfo ["predecessor"] False omit)
        return $ case token of
          TokenTrav -> AnalysisTrav $ ConsSuc $ runIdentity !<$> (getAnalysisTrav rt)
          TokenTC -> AnalysisTC $ hs2type $ NatType
          TokenRel -> AnalysisRel

      ConsRefl tyAmbient t -> do
        rtyAmbient <- h Identity
          _
          (\ gamma' -> \ case
              Classification (ConsRefl tyAmbient' t') U1 _ ->
                Just $ Identity !<$> Classification tyAmbient' U1 (ClassifWillBe U1)
              otherwise -> Nothing
          )
          extCtxId
          (fmapCoe Identity)
          (AddressInfo ["ambient type"] False omit)
        rt <- h Identity
          _
          (\ gamma' -> \ case
              Classification (ConsRefl tyAmbient' t') U1 _ ->
                Just $ Identity !<$> Classification t' U1 (ClassifMustBe tyAmbient')
              otherwise -> Nothing
          )
          extCtxId
          (fmapCoe Identity)
          (AddressInfo ["self-equand"] False omit)
        return $ case token of
          TokenTrav -> AnalysisTrav $ runIdentity !<$> ConsRefl (getAnalysisTrav rtyAmbient) (getAnalysisTrav rt)
          TokenTC -> AnalysisTC $ hs2type $ EqType tyAmbient t t
          TokenRel -> AnalysisRel

  convRel token d = modedEqDeg d
  extraClassif = U1

-------------------------

instance SysAnalyzer sys => Analyzable sys (Type sys) where
  type Classif (Type sys) = U1
  type Relation (Type sys) = ModedDegree sys
  type ClassifExtraInput (Type sys) = U1
  analyzableToken = AnTokenType
  witClassif token = Witness
  analyze token gamma (Classification (Type t) U1 maybeU1) h = Right $ do
    rt <- h Identity
      _
      (\ gamma' (Classification (Type t') U1 maybeU1') ->
         Just $ Identity !<$> Classification t' U1
           (ClassifMustBe $ hs2type $ UniHS $ unVarFromCtx <$> ctx'mode gamma'))
      extCtxId
      (fmapCoe Identity)
      (AddressInfo ["code"] True WorthMentioning)
    return $ case token of
      TokenTrav -> AnalysisTrav $ Type $ runIdentity !<$> getAnalysisTrav rt
      TokenTC -> AnalysisTC U1
      TokenRel -> AnalysisRel
    
  convRel token gamma = U1
  extraClassif = U1

-------------------------

instance SysAnalyzer sys => Analyzable sys (DependentEliminator sys) where
  type Classif (DependentEliminator sys) = U1
  type Relation (DependentEliminator sys) = ModedDegree sys
  type ClassifExtraInput (DependentEliminator sys) =
    ModedModality sys :*: Term sys :*: UniHSConstructor sys :*: (Type sys :.: VarExt)
  analyzableToken = AnTokenDependentEliminator
  witClassif token = Witness

  analyze token gamma
    (Classification clauses
      (dmuElim :*: eliminee :*: tyEliminee :*: Comp1 (motive :: Type sys (VarExt v)))
      maybeU1)
    h
    = Right $ do

    let dgamma' = ctx'mode gamma
    let dgamma = unVarFromCtx <$> dgamma'

    case (tyEliminee, clauses) of
      
      (Sigma binding, ElimSigma boundBoundPairClause) -> do
        rboundBoundPairClause <- h Identity
          _
          (\ (gamma' :: Ctx _ _ u Void)
             (Classification clauses'
               (dmuElim' :*: eliminee' :*: tyEliminee' :*: Comp1 (motive' :: Type sys (VarExt u)))
               maybeU1'
             ) -> case (tyEliminee', clauses') of
               (Sigma binding', ElimSigma boundBoundPairClause') ->
                 let segFst' = Declaration
                       (DeclNameSegment Nothing)
                       (compModedModality dmuElim' (_segment'modty $ binding'segment $ binding'))
                       Explicit
                       (_segment'content $ binding'segment $ binding')
                     segSnd' = Declaration
                       (DeclNameSegment Nothing)
                       (VarWkn <$> dmuElim')
                       Explicit
                       (binding'body binding')
                     subst VarLast = Expr2 $ TermCons $ Pair
                       (VarWkn . VarWkn <$> binding')
                       (Var2 $ VarWkn VarLast)
                       (Var2 VarLast)
                     subst (VarWkn v) = Var2 $ VarWkn $ VarWkn v
                 in  Just $ Identity !<$> Classification
                       boundBoundPairClause'
                       (segFst' :*: Comp1 (segSnd' :*: Comp1 U1))
                       (ClassifMustBe $ ClassifBinding segFst' $ ClassifBinding segSnd' $
                         swallow $ subst <$> motive'
                       )
               otherwise -> Nothing
          )
          extCtxId
          (Comp1 . Comp1 . fmap (VarWkn . VarWkn . Identity))
          (AddressInfo ["pair clause"] False omit)
        return $ case token of
          TokenTrav -> AnalysisTrav $ ElimSigma $ runIdentity !<$> getAnalysisTrav rboundBoundPairClause
          TokenTC -> AnalysisTC U1
          TokenRel -> AnalysisRel
      (_, ElimSigma _) -> unreachable

      (BoxType seg, ElimBox boundBoxClause) -> do
        rboundBoxClause <- h Identity
          _
          (\ (gamma' :: Ctx _ _ u Void)
             (Classification clauses'
               (dmuElim' :*: eliminee' :*: tyEliminee' :*: Comp1 (motive' :: Type sys (VarExt u)))
               maybeU1'
             ) -> case (tyEliminee', clauses') of
               (BoxType seg', ElimBox boundBoxClause') ->
                 let segUnbox' = Declaration
                       (DeclNameSegment Nothing)
                       (compModedModality dmuElim' (_segment'modty $ seg'))
                       Explicit
                       (_segment'content seg')
                     subst VarLast = Expr2 $ TermCons $ ConsBox (VarWkn <$> seg') (Var2 VarLast)
                     subst (VarWkn v) = Var2 $ VarWkn v
                 in  Just $ Identity !<$> Classification
                       boundBoxClause'
                       (segUnbox' :*: Comp1 U1)
                       (ClassifMustBe $ ClassifBinding segUnbox' $
                         swallow $ subst <$> motive'
                       )
               otherwise -> Nothing
          )
          extCtxId
          (Comp1 . fmap (VarWkn . Identity))
          (AddressInfo ["box clause"] False omit)
        return $ case token of
          TokenTrav -> AnalysisTrav $ ElimBox $ runIdentity !<$> getAnalysisTrav rboundBoxClause
          TokenTC -> AnalysisTC U1
          TokenRel -> AnalysisRel
      (_, ElimBox _) -> unreachable

      (EmptyType, ElimEmpty) -> pure $ case token of
        TokenTrav -> AnalysisTrav ElimEmpty
        TokenTC -> AnalysisTC U1
        TokenRel -> AnalysisRel
      (_, ElimEmpty) -> unreachable
      
      (NatType, ElimNat (zeroClause :: Term sys v) boundBoundSucClause) -> do
        rzeroClause <- h Identity
          _
          (\ (gamma' :: Ctx _ _ u Void)
             (Classification clauses'
               (dmuElim' :*: eliminee' :*: tyEliminee' :*: Comp1 (motive' :: Type sys (VarExt u)))
               maybeU1'
             ) -> case (tyEliminee', clauses') of
               (NatType, ElimNat zeroClause' boundBoundSucClause') ->
                 Just $ Identity !<$> Classification zeroClause' U1
                 (ClassifMustBe $ substLast2 (Expr2 $ TermCons $ ConsZero :: Term sys u) $ motive')
               otherwise -> Nothing
          )
          extCtxId
          (fmapCoe Identity)
          (AddressInfo ["zero clause"] False omit)
        rboundBoundSucClause <- h Identity
          _
          (\ (gamma' :: Ctx _ _ u Void)
             (Classification clauses'
               (dmuElim' :*: eliminee' :*: tyEliminee' :*: Comp1 (motive' :: Type sys (VarExt u)))
               maybeU1'
             ) -> case (tyEliminee', clauses') of
               (NatType, ElimNat zeroClause' boundBoundSucClause') ->
                 let segPred' = Declaration
                       (DeclNameSegment $ Nothing)
                       dmuElim'
                       Explicit
                       (hs2type $ NatType)
                     segHyp' = Declaration
                       (DeclNameSegment $ Nothing)
                       (idModedModality $ VarWkn . unVarFromCtx <$> ctx'mode gamma')
                       Explicit
                       motive'
                     substS :: VarExt u -> Term sys (VarExt (VarExt u))
                     substS VarLast = Expr2 $ TermCons $ ConsSuc $ Var2 $ VarWkn VarLast
                     substS (VarWkn v) = Var2 $ VarWkn $ VarWkn v
                 in  Just $ Identity !<$> Classification
                       boundBoundSucClause'
                       (segPred' :*: Comp1 (segHyp' :*: Comp1 U1))
                       (ClassifMustBe $ ClassifBinding segPred' $ ClassifBinding segHyp' $
                         swallow $ substS <$> motive'
                       )
               otherwise -> Nothing
          )
          extCtxId
          (Comp1 . Comp1 . fmap (VarWkn . VarWkn . Identity))
          (AddressInfo ["successor clause"] False omit)
        return $ case token of
          TokenTrav ->
            AnalysisTrav $ runIdentity !<$> ElimNat (getAnalysisTrav rzeroClause) (getAnalysisTrav rboundBoundSucClause)
          TokenTC -> AnalysisTC U1
          TokenRel -> AnalysisRel
      (_, ElimNat _ _) -> unreachable

  convRel token gamma = U1
  extraClassif = U1

-------------------------

instance SysAnalyzer sys => Analyzable sys (Eliminator sys) where
  type Classif (Eliminator sys) = Type sys
  type Relation (Eliminator sys) = ModedDegree sys
  type ClassifExtraInput (Eliminator sys) = ModedModality sys :*: Term sys :*: UniHSConstructor sys
  analyzableToken = AnTokenEliminator
  witClassif token = Witness

  analyze token gamma (Classification eliminator (dmuElim :*: eliminee :*: tyEliminee) _) h =
    Right $ do

    let dgamma' = ctx'mode gamma
    let dgamma = unVarFromCtx <$> dgamma'

    case (tyEliminee, eliminator) of

      (Pi binding, App arg) -> do
        rarg <- h Identity
          _
          (\ gamma' (Classification eliminator' (dmuElim' :*: eliminee' :*: tyEliminee') _) ->
             case (tyEliminee', eliminator') of
               (Pi binding', App arg') ->
                 Just $ Identity !<$> Classification arg' U1
                 (ClassifMustBe $ _segment'content $ binding'segment binding')
               otherwise -> Nothing
          )
          (\ token' gamma' (Classification eliminator' (dmuElim' :*: eliminee' :*: tyEliminee') _) _ ->
             case (tyEliminee', eliminator') of
               (Pi binding', App arg') ->
                 Just $ CtxId $ VarFromCtx <$> _segment'modty (binding'segment binding') :\\ gamma'
               otherwise -> Nothing
          )
          (fmapCoe Identity . modedDivDeg (_segment'modty $ binding'segment binding))
          (AddressInfo ["argument"] False omit)
        return $ case token of
          TokenTrav -> AnalysisTrav $ App $ runIdentity !<$> getAnalysisTrav rarg
          TokenTC -> AnalysisTC $ substLast2 arg $ binding'body binding
          TokenRel -> AnalysisRel
      (_, App arg) -> unreachable

      (Sigma binding, Fst) -> pure $ case token of
          TokenTrav -> AnalysisTrav $ Fst
          TokenTC -> AnalysisTC $ _segment'content $ binding'segment binding
          TokenRel -> AnalysisRel
      (_, Fst) -> unreachable

      (Sigma binding, Snd) -> pure $ case token of
        TokenTrav -> AnalysisTrav $ Snd
        TokenTC -> AnalysisTC $
          substLast2 (Expr2 $
            TermElim
              (modedApproxLeftAdjointProj $ _segment'modty $ binding'segment binding)
              eliminee
              (Sigma binding)
              Fst
            ) $
          binding'body binding
        TokenRel -> AnalysisRel
      (_, Snd) -> unreachable

      (BoxType seg, Unbox) -> pure $ case token of
        TokenTrav -> AnalysisTrav $ Unbox
        TokenTC -> AnalysisTC $ _segment'content seg
        TokenRel -> AnalysisRel
      (_, Unbox) -> unreachable

      (Pi binding, Funext) -> pure $ case token of
        TokenTrav -> AnalysisTrav $ Funext
        TokenTC -> case binding'body binding of
          TypeHS (EqType tyAmbient tL tR) -> AnalysisTC $ hs2type $ EqType
            (hs2type $ Pi $           Binding (binding'segment binding) tyAmbient)
            (Expr2 $ TermCons $ Lam $ Binding (binding'segment binding) tL)
            (Expr2 $ TermCons $ Lam $ Binding (binding'segment binding) tR)
          _ -> unreachable
        TokenRel -> AnalysisRel
      (_, Funext) -> unreachable

      (_, ElimDep boundMotive@(NamedBinding name motive) clauses) -> do
        rboundMotive <- h Identity
          _
          (\ gamma' (Classification eliminator' (dmuElim' :*: eliminee' :*: tyEliminee') _) ->
             case (tyEliminee', eliminator') of
               (_, ElimDep boundMotive' clauses') ->
                 let seg' = Declaration (DeclNameSegment Nothing) dmuElim' Explicit
                       (hs2type tyEliminee')
                 in  Just $ Identity !<$> Classification boundMotive'
                       (seg' :*: Comp1 U1)
                       (ClassifWillBe $ ClassifBinding seg' U1)
               otherwise -> Nothing
          )
          extCtxId
          (Comp1 . fmap (VarWkn . Identity))
          (AddressInfo ["motive"] False omit)
        rclauses <- h Identity
          _
          (\ gamma' (Classification eliminator' (dmuElim' :*: eliminee' :*: tyEliminee') _) ->
             case (tyEliminee', eliminator') of
               (_, ElimDep (NamedBinding name' motive') clauses') ->
                 Just $ Identity !<$> Classification clauses'
                       (dmuElim' :*: eliminee' :*: tyEliminee' :*: Comp1 motive')
                       (ClassifWillBe U1)
               otherwise -> Nothing
          )
          extCtxId
          (fmapCoe Identity)
          (AddressInfo ["clauses"] False EntirelyBoring)
        return $ case token of
          TokenTrav ->
            AnalysisTrav $ runIdentity !<$> ElimDep (getAnalysisTrav rboundMotive) (getAnalysisTrav rclauses)
          TokenTC -> AnalysisTC $ substLast2 eliminee motive
          TokenRel -> AnalysisRel
          
      (EqType tyAmbient tL tR, ElimEq boundBoundMotive clauseRefl) -> do
        rboundBoundMotive <- h Identity
          _
          (\ gamma' (Classification eliminator' (dmuElim' :*: eliminee' :*: tyEliminee') _) ->
             case (tyEliminee', eliminator') of
               (EqType tyAmbient' tL' tR', ElimEq boundBoundMotive' clauseRefl') ->
                 let segR' = Declaration (DeclNameSegment Nothing) dmuElim' Explicit tyAmbient'
                     segEq' = Declaration
                       (DeclNameSegment Nothing)
                       (VarWkn <$> dmuElim')
                       Explicit
                       (hs2type $ EqType (VarWkn <$> tyAmbient') (VarWkn <$> tL') (Var2 VarLast))
                 in  Just $ Identity !<$> Classification boundBoundMotive'
                       (segR' :*: Comp1 (segEq' :*: Comp1 U1))
                       (ClassifWillBe $ ClassifBinding segR' $ ClassifBinding segEq' $ U1)
               otherwise -> Nothing
          )
          extCtxId
          (Comp1 . Comp1 . fmap (VarWkn . VarWkn . Identity))
          (AddressInfo ["motive"] False omit)
        rclauseRefl <- h Identity
          _
          (\ gamma' (Classification eliminator' (dmuElim' :*: eliminee' :*: tyEliminee') _) ->
             case (tyEliminee', eliminator') of
               (EqType tyAmbient' tL' tR', ElimEq boundBoundMotive' clauseRefl') ->
                 Just $ Identity !<$> Classification clauseRefl' U1
                   (ClassifMustBe $
                     substLast2 tL' $
                     substLast2 (Expr2 $ TermCons $ VarWkn <$> ConsRefl tyAmbient' tL') $
                     _namedBinding'body $ _namedBinding'body $ boundBoundMotive'
                   )
               otherwise -> Nothing
          )
          extCtxId
          (fmapCoe Identity)
          (AddressInfo ["refl clause"] False omit)
        return $ case token of
           TokenTrav ->
             AnalysisTrav $ runIdentity !<$> ElimEq (getAnalysisTrav rboundBoundMotive) (getAnalysisTrav rclauseRefl)
           TokenTC -> AnalysisTC $ substLast2 tR $ substLast2 (VarWkn <$> eliminee) $
             _namedBinding'body $ _namedBinding'body $ boundBoundMotive
           TokenRel -> AnalysisRel
      (_, ElimEq _ _) -> unreachable

  convRel token d = modedEqDeg d
  extraClassif = U1

-------------------------

instance SysAnalyzer sys => Analyzable sys (TermNV sys) where
  type Classif (TermNV sys) = Type sys
  type Relation (TermNV sys) = ModedDegree sys
  type ClassifExtraInput (TermNV sys) = U1
  analyzableToken = AnTokenTermNV
  witClassif token = Witness

  analyze token gamma (Classification t U1 maybeTy) h = case t of

    TermCons c -> Right $ do
      rc <- h Identity
        _
        (\ gamma' -> \ case
            (Classification (TermCons c') U1 maybeTy') ->
              Just $ Identity !<$> Classification c' U1 (classifMust2will maybeTy')
            otherwise -> Nothing
        )
        extCtxId
        (fmapCoe Identity)
        (AddressInfo ["underlying constructor"] False EntirelyBoring)
      return $ case token of
        TokenTrav -> AnalysisTrav $ TermCons $ runIdentity !<$> getAnalysisTrav rc
        TokenTC -> AnalysisTC $ runIdentity !<$> getAnalysisTC rc
        TokenRel -> AnalysisRel

    TermElim dmuElim eliminee tyEliminee eliminator -> Right $ do
      rdmuElim <- h Identity
        _
        (\ gamma' -> \ case
            (Classification (TermElim dmuElim' eliminee' tyEliminee' eliminator') U1 maybeTy') ->
              Just $ Identity !<$> Classification dmuElim' U1
                (ClassifMustBe $ modality'dom dmuElim' :*: (unVarFromCtx <$> ctx'mode gamma'))
            otherwise -> Nothing
        )
        crispExtCtxId
        (const $ Const ModEq)
        (AddressInfo ["modality of elimination"] False omit)
      reliminee <- h Identity
        _
        (\ gamma' -> \ case
            (Classification (TermElim dmuElim' eliminee' tyEliminee' eliminator') U1 maybeTy') ->
              Just $ Identity !<$> Classification eliminee' U1 (ClassifMustBe $ hs2type tyEliminee')
            otherwise -> Nothing
        )
        (\ token' gamma' input1 condInput2 -> case input1 of
            (Classification (TermElim dmuElim' eliminee' tyEliminee' eliminator') U1 maybeTy') ->
              Just $ CtxId $ VarFromCtx <$> dmuElim' :\\ gamma'
            otherwise -> Nothing
        )
        (fmapCoe Identity . modedDivDeg dmuElim)
        (AddressInfo ["eliminee"] True omit)
      rtyEliminee <- h Identity
        _
        (\ gamma' -> \ case
            (Classification (TermElim dmuElim' eliminee' tyEliminee' eliminator') U1 maybeTy') ->
              Just $ Identity !<$> Classification tyEliminee' U1 (ClassifMustBe $ unVarFromCtx <$> ctx'mode gamma')
            otherwise -> Nothing
        )
        (\ token' gamma' input1 condInput2 -> case input1 of
            (Classification (TermElim dmuElim' eliminee' tyEliminee' eliminator') U1 maybeTy') ->
              Just $ CtxId $ VarFromCtx <$> dmuElim' :\\ gamma'
            otherwise -> Nothing
        )
        (fmapCoe Identity . modedDivDeg dmuElim)
        (AddressInfo ["type of eliminee"] False omit)
      reliminator <- h Identity
        _
        (\ gamma' -> \ case
            (Classification (TermElim dmuElim' eliminee' tyEliminee' eliminator') U1 maybeTy') ->
              Just $ Identity !<$> Classification
                eliminator'
                (dmuElim' :*: eliminee' :*: tyEliminee')
                ClassifUnknown
            otherwise -> Nothing
        )
        extCtxId
        (fmapCoe Identity)
        (AddressInfo ["eliminator"] False EntirelyBoring)
      return $ case token of
        TokenTrav ->
          AnalysisTrav $ runIdentity !<$> TermElim (getAnalysisTrav rdmuElim) (getAnalysisTrav reliminee) (getAnalysisTrav rtyEliminee) (getAnalysisTrav reliminator)
        TokenTC -> AnalysisTC $ runIdentity !<$> getAnalysisTC reliminator
        TokenRel -> AnalysisRel

    TermMeta _ _ _ _ -> Left AnErrorTermMeta

    TermWildcard -> Left AnErrorTermWildcard

    TermQName _ _ -> Left AnErrorTermQName

    TermAlreadyChecked t ty -> Left AnErrorTermAlreadyChecked
      {-Just $ do
      rt <- h id gamma (Classification t U1 (Just ty) maybeRel)
      rty <- h id gamma (Classification ty U1 (Just U1) maybeRel)
      return $ case token of
        TokenTrav -> AnalysisTrav $ -}

    TermAlgorithm _ _ -> Left AnErrorTermAlgorithm

    TermSys syst -> Right $ do
      _
      rsyst <- h Identity
        (\ gamma' -> \ case
            (Classification (TermSys syst') U1 maybeTy') ->
              Just $ Identity !<$> Classification syst' U1 (classifMust2will maybeTy')
            otherwise -> Nothing
        )
        extCtxId
        (fmapCoe Identity)
        (AddressInfo ["system-specific term"] True EntirelyBoring)
      return $ case token of
        TokenTrav -> AnalysisTrav $ TermSys $ runIdentity !<$> getAnalysisTrav rsyst
        TokenTC -> AnalysisTC $ runIdentity !<$> getAnalysisTC rsyst
        TokenRel -> AnalysisRel

    TermProblem t -> Left AnErrorTermProblem
    
  convRel token d = modedEqDeg d
  extraClassif = U1

-------------------------

instance SysAnalyzer sys => Analyzable sys (Term sys) where
  type Classif (Term sys) = Type sys
  type Relation (Term sys) = ModedDegree sys
  type ClassifExtraInput (Term sys) = U1
  analyzableToken = AnTokenTerm
  witClassif token = Witness
  analyze token gamma (Classification t U1 maybeTy) h = case t of
    Expr2 tnv -> Right $ do
      rtnv <- h Identity
        _
        (\ gamma' -> \ case
            (Classification (Expr2 tnv') U1 maybeTy') ->
              Just $ Identity !<$> Classification tnv' U1 (classifMust2will maybeTy')
            otherwise -> Nothing
        )
        extCtxId
        (fmapCoe Identity)
        (AddressInfo ["non-variable"] True EntirelyBoring)
      return $ case token of
        TokenTrav -> AnalysisTrav $ Expr2 $ runIdentity !<$> getAnalysisTrav rtnv
        TokenTC -> AnalysisTC $ runIdentity !<$> getAnalysisTC rtnv
        TokenRel -> AnalysisRel
    Var2 v -> Left AnErrorVar
  convRel token d = modedEqDeg d
  extraClassif = U1

-------------------------

instance (SysAnalyzer sys, Analyzable sys (rhs sys)) => Analyzable sys (Declaration declSort rhs sys) where
  type Classif (Declaration declSort rhs sys) = Classif (rhs sys)
  type Relation (Declaration declSort rhs sys) = Relation (rhs sys)
  type ClassifExtraInput (Declaration declSort rhs sys) = ClassifExtraInput (rhs sys)
  analyzableToken = AnTokenDeclaration analyzableToken
  witClassif token = haveClassif @sys @(rhs sys) Witness
  analyze token gamma (Classification decl@(Declaration name dmu plic content) extraContent maybeTyContent) h = Right $ do
    rdmu <- h Identity
      _
      (\ gamma' (Classification decl'@(Declaration name' dmu' plic' content') extraContent' maybeTyContent') ->
         Just $ Identity !<$>
         Classification dmu' U1 (ClassifMustBe $ modality'dom dmu' :*: (unVarFromCtx <$> ctx'mode gamma')))
      crispExtCtxId
      (const $ Const $ ModEq)
      (AddressInfo ["modality"] True omit)
    rcontent <- h Identity
      _
      (\ gamma' (Classification decl'@(Declaration name' dmu' plic' content') extraContent' maybeTyContent') ->
         Just $ Identity !<$>
         Classification content' extraContent' (classifMust2will maybeTyContent'))
      (\ token' gamma' (Classification decl'@(Declaration name' dmu' plic' content') extraContent' maybeTyContent') _ ->
         Just $ CtxId $ VarFromCtx <$> dmu' :\\ gamma'
      )
      (fmapCoe Identity)
      (AddressInfo ["type"] True omit)
    return $ case token of
      TokenTrav -> AnalysisTrav $ runIdentity !<$> Declaration name (getAnalysisTrav rdmu) (Identity !<$> _plic) (getAnalysisTrav rcontent)
      TokenTC -> AnalysisTC $ runIdentity !<$> getAnalysisTC rcontent
      TokenRel -> AnalysisRel
  {-
  analyze token fromType gamma (Classification seg@(Declaration name dmu plic ty) extra maybeTy maybeRel) h = Right $ do
    let dgamma' = ctx'mode gamma
    let dgamma = unVarFromCtx <$> dgamma'
    
    rdmu <- h id (crispModedModality dgamma' :\\ gamma)
      (Classification dmu U1 (ClassifMustBe $ modality'dom dmu :*: dgamma) (toIfRel token $ Const ModEq))
      (AddressInfo ["modality"] True omit)
      (Just . _decl'modty)
    -- TODO plic
    rty <- h id (VarFromCtx <$> dmu :\\ gamma)
      (Classification ty extra (classifMust2will maybeTy) maybeRel)
      (AddressInfo ["type"] True omit)
      (Just . _decl'content)

    return $ case token of
      TokenTrav -> AnalysisTrav $ Declaration name (getAnalysisTrav rdmu) plic (getAnalysisTrav rty)
      TokenTC -> AnalysisTC $ getAnalysisTC rty
      TokenRel -> AnalysisRel
-}
  convRel token d = convRel (analyzableToken @sys @(rhs sys)) d
  extraClassif = extraClassif @sys @(rhs sys)

-------------------------

instance (SysAnalyzer sys,
          Analyzable sys (rhs sys),
          Classif (rhs sys) ~ U1,
          ClassifExtraInput (rhs sys) ~ U1,
          Relation (rhs sys) ~ ModedDegree sys) => Analyzable sys (Telescoped Type rhs sys) where
  type Classif (Telescoped Type rhs sys) = U1
  type Relation (Telescoped Type rhs sys) = Relation (Type sys) :*: Relation (rhs sys)
  type ClassifExtraInput (Telescoped Type rhs sys) = U1
  analyzableToken = AnTokenTelescoped analyzableToken
  witClassif token = Witness
  
  analyze token gamma (Classification telescopedRHS U1 maybeU1) h = Right $ do
    case telescopedRHS of
      
      Telescoped rhs -> do
        rrhs <- h Identity
          _
          (\ gamma -> \ case
              (Classification (Telescoped rhs') U1 maybeU1') ->
                Just $ Identity !<$> Classification rhs' U1 (ClassifWillBe U1)
              otherwise -> Nothing
          )
          extCtxId
          (fmapCoe Identity . snd1)
          (AddressInfo ["rhs"] True omit)
        return $ case token of
          TokenTrav -> AnalysisTrav $ Telescoped $ runIdentity !<$> getAnalysisTrav rrhs
          TokenTC -> AnalysisTC U1
          TokenRel -> AnalysisRel
          
      (seg :|- telescopedRHS) -> do
        rseg <- h Identity
          _
          (\ gamma -> \ case
              (Classification (seg' :|- telescopedRHS') U1 maybeU1') ->
                Just $ Identity !<$> Classification seg' U1 (ClassifWillBe U1)
              otherwise -> Nothing
          )
          extCtxId
          (fmapCoe Identity . fst1)
          (AddressInfo ["a segment"] True omit)
        rtelescopedRHS <- h VarWkn
          _
          (\ gamma' -> \ case
              (Classification (seg' :|- telescopedRHS') U1 maybeU1') ->
                Just $ Classification telescopedRHS' U1 (ClassifWillBe U1)
              otherwise -> Nothing
          )
          (\ token' gamma' input1 condInput2 -> case input1 of
              (Classification (seg' :|- telescopedRHS') U1 maybeU1') -> case token' of
                TokenFalse -> Just $ gamma' :.. VarFromCtx <$> seg'
                TokenTrue  -> runConditional condInput2 & \ case
                  (Classification (seg2 :|- telescopedRHS2) U1 maybeU12) ->
                    Just $ gamma' :.. VarFromCtx <$> (seg' & decl'content %~
                      \ ty1 -> Twice2 ty1 $ _decl'content seg2
                    )
                  otherwise -> Nothing
              otherwise -> Nothing
          )
          (fmap VarWkn)
          (AddressInfo ["tail"] True EntirelyBoring)
        return $ case token of
          TokenTrav -> AnalysisTrav $ runIdentity !<$> getAnalysisTrav rseg :|- getAnalysisTrav rtelescopedRHS
          TokenTC -> AnalysisTC U1
          TokenRel -> AnalysisRel

      (dmu :** telescopedRHS) -> do
        rdmu <- h Identity
          _
          (\ gamma' -> \ case
              (Classification (dmu' :** telescopedRHS') U1 maybeU1') ->
                Just $ Identity !<$> Classification dmu' U1
                  (ClassifMustBe $ modality'dom dmu' :*: (unVarFromCtx <$> ctx'mode gamma'))
              otherwise -> Nothing
          )
          crispExtCtxId
          (const $ Const ModEq)
          (AddressInfo ["applied modality"] True omit)
        rtelescopedRHS <- h Identity
          _
          (\ gamma' -> \ case
              (Classification (dmu' :** telescopedRHS') U1 maybeU1') ->
                Just $ Identity !<$> Classification telescopedRHS' U1 (ClassifWillBe U1)
              otherwise -> Nothing
          )
          (\ token' gamma' input1 condInput2 -> case input1 of
              (Classification (dmu' :** telescopedRHS') U1 maybeU1') ->
                Just $ CtxId $ VarFromCtx <$> dmu' :\\ gamma'
              otherwise -> Nothing
          )
          (fmapCoe Identity . (\ (ddegSeg :*: ddegRHS) -> modedDivDeg dmu ddegSeg :*: modedDivDeg dmu ddegRHS))
          (AddressInfo ["tail"] True EntirelyBoring)
        return $ case token of
          TokenTrav -> AnalysisTrav $ runIdentity !<$> getAnalysisTrav rdmu :** getAnalysisTrav rtelescopedRHS
          TokenTC -> AnalysisTC U1
          TokenRel -> AnalysisRel

  convRel token d = U1
  extraClassif = U1

-------------------------

instance SysAnalyzer sys => Analyzable sys (ValRHS sys) where
  type Classif (ValRHS sys) = U1
  type Relation (ValRHS sys) = ModedDegree sys
  type ClassifExtraInput (ValRHS sys) = U1
  analyzableToken = AnTokenValRHS
  witClassif token = Witness
  analyze token gamma (Classification valRHS@(ValRHS t ty) U1 maybeU1) h = Right $ do
    rty <- h Identity
      _
      (\ gamma' (Classification valRHS@(ValRHS t' ty') U1 maybeU1') ->
         Just $ Identity !<$> Classification ty' U1 (ClassifWillBe U1))
      extCtxId
      (fmapCoe Identity)
      (AddressInfo ["type"] True omit)
    rt <- h Identity
      _
      (\ gamma' (Classification valRHS@(ValRHS t' ty') U1 maybeU1') ->
         Just $ Identity !<$> Classification t' U1 (ClassifMustBe ty'))
      extCtxId
      (fmapCoe Identity)
      (AddressInfo ["RHS"] True omit)
    return $ case token of
      TokenTrav -> AnalysisTrav $ runIdentity !<$> ValRHS (getAnalysisTrav rt) (getAnalysisTrav rty)
      TokenTC -> AnalysisTC $ U1
      TokenRel -> AnalysisRel
  convRel token d = U1
  extraClassif = U1

-------------------------

instance SysAnalyzer sys => Analyzable sys (ModuleRHS sys) where
  type Classif (ModuleRHS sys) = U1
  type Relation (ModuleRHS sys) = ModedDegree sys
  type ClassifExtraInput (ModuleRHS sys) = U1
  analyzableToken = AnTokenModuleRHS
  witClassif token = Witness

  analyze token gamma (Classification moduleRHS@(ModuleRHS (Compose revEntries)) U1 maybeU1) h = Right $ do
    let n = length revEntries
    rrevEntries <- fmap reverse . sequenceA $
      zip4 (reverse revEntries) (reverse $ tails revEntries) [n-1, n-2..] [0..] <&>
      \ (entry, revPrevEntries, indexRev, index) ->
      h VarInModule
        _
        (\ gamma' (Classification moduleRHS'@(ModuleRHS (Compose revEntries')) U1 maybeU1') ->
           Just $ Classification (revEntries' !! indexRev) U1 (ClassifWillBe U1))
        (\ token' gamma' (Classification moduleRHS'@(ModuleRHS (Compose revEntries')) U1 maybeU1') _ ->
           Just $ gamma' :<...> VarFromCtx <$> ModuleRHS (Compose $ tails revEntries' !! indexRev))
        (fmapCoe VarInModule)
        (AddressInfo [show (index + 1) ++ "th entry"] True omit)
    return $ case token of
      TokenTrav -> AnalysisTrav $ ModuleRHS $ Compose $ getAnalysisTrav <$> rrevEntries
      TokenTC -> AnalysisTC $ U1
      TokenRel -> AnalysisRel
      
  convRel token d = U1
  extraClassif = U1

-------------------------

{-
instance SysAnalyzer sys => Analyzable (Val sys) where
  type Classif (Val sys) = U1
  type Relation (Val sys) = ModedDegree sys
  type ClassifExtraInput (Val sys) = U1
  analyze token fromType h gamma (Classification val@(Declaration ))
-}

------------------------

instance SysAnalyzer sys => Analyzable sys (Entry sys) where
  type Classif (Entry sys) = U1
  type Relation (Entry sys) = ModedDegree sys
  type ClassifExtraInput (Entry sys) = U1
  analyzableToken = AnTokenEntry
  witClassif token = Witness
  analyze token gamma (Classification entry U1 maybeU1) h = Right $ do
    case entry of
      EntryVal val -> do
        rval <- h Identity
          _
          (\ gamma' -> \ case
              (Classification (EntryVal val') U1 maybeU1') ->
                Just $ Identity !<$> Classification val' U1 (ClassifWillBe U1)
              otherwise -> Nothing
          )
          extCtxId
          ((\ ddeg -> ddeg :*: ddeg) . fmapCoe Identity)
          (AddressInfo ["val"] True EntirelyBoring)
        return $ case token of
          TokenTrav -> AnalysisTrav $ EntryVal $ runIdentity !<$> getAnalysisTrav rval
          TokenTC -> AnalysisTC $ U1
          TokenRel -> AnalysisRel
      EntryModule modul -> do
        rmodul <- h Identity
          _
          (\ gamma' -> \ case
              (Classification (EntryModule modul') U1 maybeU1') ->
                Just $ Identity !<$> Classification modul' U1 (ClassifWillBe U1)
              otherwise -> Nothing
          )
          extCtxId
          ((\ ddeg -> ddeg :*: ddeg) . fmapCoe Identity)
          (AddressInfo ["module"] True EntirelyBoring)
        return $ case token of
          TokenTrav -> AnalysisTrav $ EntryModule $ runIdentity !<$> getAnalysisTrav rmodul
          TokenTC -> AnalysisTC $ U1
          TokenRel -> AnalysisRel
        
  convRel token d = U1
  extraClassif = U1

------------------------
------------------------

instance (SysAnalyzer sys) => Analyzable sys U1 where
  type Classif U1 = U1
  type Relation U1 = U1
  type ClassifExtraInput U1 = U1
  analyzableToken = AnTokenU1
  witClassif token = Witness
  analyze token gamma (Classification U1 U1 _) h =
    Right $ pure $ case token of
        TokenTrav -> AnalysisTrav $ U1
        TokenTC -> AnalysisTC $ U1
        TokenRel -> AnalysisRel
  convRel token d = U1
  extraClassif = U1

------------------------

instance (SysAnalyzer sys,
          Analyzable sys f,
          Analyzable sys g) => Analyzable sys (f :*: g) where
  type Classif (f :*: g) = Classif f :*: Classif g
  type Relation (f :*: g) = Relation f :*: Relation g
  type ClassifExtraInput (f :*: g) = ClassifExtraInput f :*: ClassifExtraInput g
  analyzableToken = AnTokenPair1 analyzableToken analyzableToken
  witClassif token = 
    haveClassif @sys @f $
    haveClassif @sys @g $ Witness

  analyze token gamma (Classification (fv :*: gv) (extraF :*: extraG) maybeClassifs) h = Right $ do
    rfv <- h Identity
      _
      (\ gamma' (Classification (fv' :*: gv') (extraF' :*: extraG') maybeClassifs') ->
         Just $ Identity !<$> Classification fv' extraF' (fst1 <$> maybeClassifs'))
      extCtxId
      (fmapCoe Identity . fst1)
      (AddressInfo ["first component"] True omit)
    rgv <- h Identity
      _
      (\ gamma' (Classification (fv' :*: gv') (extraF' :*: extraG') maybeClassifs') ->
         Just $ Identity !<$> Classification gv' extraG' (snd1 <$> maybeClassifs'))
      extCtxId
      (fmapCoe Identity . snd1)
      (AddressInfo ["second component"] True omit)
    return $ case token of
      TokenTrav -> AnalysisTrav $ runIdentity !<$> getAnalysisTrav rfv :*: getAnalysisTrav rgv
      TokenTC -> AnalysisTC $ runIdentity !<$> getAnalysisTC rfv :*: getAnalysisTC rgv
      TokenRel -> AnalysisRel
  convRel token d = convRel (analyzableToken @sys @f) d :*:
                    convRel (analyzableToken @sys @g) d
  extraClassif = extraClassif @sys @f :*:
                 extraClassif @sys @g

------------------------

{-
instance (SysAnalyzer sys,
          Analyzable sys t,
          Analyzable sys (Classif t),
          Applicative f) => Analyzable sys (Compose f t) where
  type Classif (Compose f t) = Classif t
  type Relation (Compose f t) = Relation t
  type ClassifExtraInput (Compose f t) = Compose f (ClassifExtraInput t)
  analyzableToken = AnTokenCompose analyzableToken
  analyze token fromType gamma (Classification (Compose ftv) (Compose fextra) maybeClassifs maybeRel) h = Right $ do
    return $ case token of
      TokenTrav -> 
-}

------------------------

{-
instance (SysAnalyzer sys,
          Analyzable sys f,
          Functor g) => Analyzable sys (f :.: g) where
  type Classif (f :.: g) = Classif f :.: g
  type Relation (f :.: g) = Relation f :.: g
  type ClassifExtraInput (f :.: g) = ClassifExtraInput f :.: g
  analyze token fromType h gamma (Classification (Comp1 fgv) (Comp1 extra) maybeCompClassif maybeCompRel) = do
    analyze <- analyze token fromType _h gamma
      (Classification fgv extra (unComp1 <$> maybeCompClassif) (unComp1 <$> maybeCompRel))
    return $ do
      rfgv <- analyze
      return $ case token of
        TokenTrav -> AnalysisTrav $ Comp1 $ getAnalysisTrav rfgv
        TokenTC -> AnalysisTC $ Comp1 $ getAnalysisTC rfgv
        TokenRel -> AnalysisRel
-}

------------------------
