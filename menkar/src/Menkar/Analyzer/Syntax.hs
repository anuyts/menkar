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
  type AnalyzerExtraInput (ModedModality sys) = U1
  analyzableToken = AnTokenModedModality
  witClassif token = Witness
  analyze token gamma (AnalyzerInput (ModedModality dom cod mu) U1 _) h = Right $ do
    rdom <- h Identity
      (\ gamma' (AnalyzerInput (ModedModality dom' cod' mu') U1 _) ->
         Just $ Identity !<$> AnalyzerInput dom' U1 (ClassifWillBe U1))
      extCtxId
      (const U1)
      (AddressInfo ["domain"] True omit)
    rcod <- h Identity
      (\ gamma' (AnalyzerInput (ModedModality dom' cod' mu') U1 _) ->
         Just $ Identity !<$> AnalyzerInput cod' U1 (ClassifWillBe U1))
      extCtxId
      (const U1)
      (AddressInfo ["codomain"] True omit)
    rmu <- h Identity
      (\ gamma' (AnalyzerInput (ModedModality dom' cod' mu') U1 _) ->
         Just $ Identity !<$> AnalyzerInput mu' U1 (ClassifWillBe $ dom' :*: cod'))
      extCtxId
      (fmapCoe Identity)
      (AddressInfo ["modality"] True omit)
    return $ case token of
        TokenSubASTs ->
          Box1 $ runIdentity !<$> ModedModality (unbox1 rdom) (unbox1 rcod) (unbox1 rmu)
        TokenTypes -> BoxClassif $ dom :*: cod
        TokenRelate -> Unit2
  convRel token d = U1 :*: U1
  extraClassif = U1 :*: U1

-------------------------

instance (SysAnalyzer sys,
          Analyzable sys (rhs sys),
          Relation (rhs sys) ~ ModedDegree sys,
          AnalyzerExtraInput (rhs sys) ~ U1,
          AnalyzerExtraInput (Classif (rhs sys)) ~ U1
         ) => Analyzable sys (Binding Type rhs sys) where
  type Classif (Binding Type rhs sys) = Classif (Segment Type sys) :*: ClassifBinding Type (Classif (rhs sys)) sys
  type Relation (Binding Type rhs sys) = ModedDegree sys
  type AnalyzerExtraInput (Binding Type rhs sys) = U1
  analyzableToken = AnTokenBinding analyzableToken
  witClassif token = haveClassif @sys @(rhs sys) Witness
  analyze token gamma (AnalyzerInput (Binding seg body) U1 maybeCl) h = Right $ do
    rseg <- h Identity
      (\ gamma' (AnalyzerInput (Binding seg' body') U1 maybeCl') ->
         Just $ Identity !<$> AnalyzerInput seg' U1 (fst1 <$> classifMust2will maybeCl'))
      extCtxId
      (fmapCoe Identity)
      (AddressInfo ["segment"] False omit)
    rbody <- h VarWkn
      (\ gamma' (AnalyzerInput (Binding seg' body') U1 maybeCl') ->
         Just $ AnalyzerInput body' U1 (_classifBinding'body . snd1 <$> classifMust2will maybeCl'))
      (\ gamma (AnalyzerInput (Binding seg1 body1) U1 maybeCl1) condInput2 ->
         Just $ gamma :..
           (decl'content %~ \ ty1 ->
             toVarClassif token ty1 $
             fmap VarFromCtx . _decl'content . binding'segment . _analyzerInput'get <$> condInput2
           )
           (VarFromCtx <$> seg1)
      )
      (fmap VarWkn)
      (AddressInfo ["body"] False omit)
    return $ case token of
      TokenSubASTs -> Box1 $ Binding (runIdentity !<$> unbox1 rseg) (unbox1 rbody)
      TokenTypes -> BoxClassif $
        (runIdentity !<$> unboxClassif rseg) :*: ClassifBinding seg (unboxClassif rbody)
      TokenRelate -> Unit2
  convRel token d = U1 :*: Comp1 (convRel (analyzableToken @sys @(rhs sys)) (VarWkn <$> d))
  extraClassif = U1 :*: Comp1 (extraClassif @sys @(rhs sys))

-------------------------

instance (SysAnalyzer sys,
          Analyzable sys rhs
          --Relation rhs ~ ModedDegree sys,
          --AnalyzerExtraInput rhs ~ U1
         ) => Analyzable sys (ClassifBinding Type rhs sys) where
  type Classif (ClassifBinding Type rhs sys) = ClassifBinding Type (Classif rhs) sys
  type Relation (ClassifBinding Type rhs sys) = Relation rhs :.: VarExt
  type AnalyzerExtraInput (ClassifBinding Type rhs sys) = AnalyzerExtraInput rhs :.: VarExt
  analyzableToken = AnTokenClassifBinding analyzableToken
  witClassif token = haveClassif @sys @rhs Witness
  analyze token gamma
    (AnalyzerInput (ClassifBinding seg body) (Comp1 extraBody) maybeCl) h = Right $ do
    rbody <- h VarWkn
      (\ gamma' (AnalyzerInput (ClassifBinding seg' body') (Comp1 extraBody') maybeCl') ->
         Just $ AnalyzerInput body' extraBody' (_classifBinding'body <$> classifMust2will maybeCl'))
      (\ gamma (AnalyzerInput (ClassifBinding seg1 body1) (Comp1 extraBody1) maybeCl1) condInput2 ->
         Just $ gamma :..
           (decl'content %~ \ ty1 ->
             toVarClassif token ty1 $
             fmap VarFromCtx . _decl'content . _classifBinding'segment . _analyzerInput'get <$>
             condInput2
           )
           (VarFromCtx <$> seg1)
      )
      unComp1
      (AddressInfo ["body"] False EntirelyBoring)
    return $ case token of
      TokenSubASTs -> Box1 $ ClassifBinding seg (unbox1 rbody)
      TokenTypes -> BoxClassif $ ClassifBinding seg (unboxClassif rbody)
      TokenRelate -> Unit2
  convRel token d = Comp1 $ convRel (analyzableToken @sys @rhs) (VarWkn <$> d)
  extraClassif = Comp1 $ extraClassif @sys @rhs

-------------------------

instance (SysAnalyzer sys,
          Analyzable sys (rhs sys)
         ) => Analyzable sys (NamedBinding rhs sys) where
  type Classif (NamedBinding rhs sys) = ClassifBinding Type (Classif (rhs sys)) sys
  type Relation (NamedBinding rhs sys) = Relation (rhs sys) :.: VarExt
  type AnalyzerExtraInput (NamedBinding rhs sys) =
    Segment Type sys :*: (AnalyzerExtraInput (rhs sys) :.: VarExt)
  analyzableToken = AnTokenNamedBinding analyzableToken
  witClassif token = haveClassif @sys @(rhs sys) Witness
  analyze token gamma
    (AnalyzerInput (NamedBinding name body) (seg :*: Comp1 extraBody) maybeCl) h = Right $ do
    rbody <- h VarWkn
      (\ gamma' (AnalyzerInput (NamedBinding name' body') (seg' :*: Comp1 extraBody') maybeCl') ->
         Just $ AnalyzerInput body' extraBody' (_classifBinding'body <$> classifMust2will maybeCl'))
      (\ gamma'
         (AnalyzerInput (NamedBinding name1 body1) (seg1 :*: Comp1 extraBody1) maybeCl1)
         condInput2 ->
         Just $ gamma' :.. VarFromCtx <$> (Declaration
           (DeclNameSegment name1)
           (_decl'modty seg1)
           (_decl'plicity seg1)
           (toVarClassif token
             (_decl'content seg1)
             (_decl'content . fst1 . _analyzerInput'extra <$> condInput2)
           )
         )
      )
      unComp1
      (AddressInfo ["body"] False EntirelyBoring)
    return $ case token of
      TokenSubASTs -> Box1 $ NamedBinding name $ unbox1 rbody
      TokenTypes -> BoxClassif $
        ClassifBinding ((decl'name .~ DeclNameSegment name) seg) (unboxClassif rbody)
      TokenRelate -> Unit2
  convRel token d = Comp1 $ convRel (analyzableToken @sys @(rhs sys)) (VarWkn <$> d)
  extraClassif = Comp1 $ extraClassif @sys @(rhs sys)

-------------------------

instance (SysAnalyzer sys) => Analyzable sys (UniHSConstructor sys) where
  
  type Classif (UniHSConstructor sys) = Mode sys
  type Relation (UniHSConstructor sys) = ModedDegree sys
  type AnalyzerExtraInput (UniHSConstructor sys) = U1
  analyzableToken = AnTokenUniHSConstructor
  witClassif token = Witness
  analyze (token :: AnalyzerToken option) gamma
    (AnalyzerInput (ty :: UniHSConstructor sys v) U1 maybeD) h = Right $ do
    
    let dgamma' = ctx'mode gamma
    let dgamma = unVarFromCtx <$> dgamma'

    case ty of

      UniHS d -> do
        rd <- h Identity
          (\ gamma' -> \ case
              (AnalyzerInput (UniHS d') U1 maybeD') ->
                Just $ Identity !<$> AnalyzerInput d' U1 (ClassifWillBe U1)
              otherwise -> Nothing
          )
          extCtxId
          (const U1)
          (AddressInfo ["mode"] False omit)
        return $ case token of
          TokenSubASTs -> Box1 $ runIdentity !<$> UniHS (unbox1 rd)
          TokenTypes -> BoxClassif $ d
          TokenRelate -> Unit2

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
              (\ gamma' (AnalyzerInput ty' U1 maybeD') -> extract ty' <&> \ segment' ->
                  Identity !<$> AnalyzerInput segment' U1 (ClassifWillBe $ U1))
              extCtxId
              (fmapCoe Identity)
              (AddressInfo ["segment"] False EntirelyBoring)
        return $ case token of
          TokenSubASTs -> Box1 $ BoxType $ runIdentity !<$> unbox1 rsegment
          TokenTypes -> BoxClassif $ dgamma
          TokenRelate -> Unit2

      NatType -> handleConstant

      EqType tyAmbient tL tR -> do
        rtyAmbient <- h Identity
          (\ gamma' -> \ case
              AnalyzerInput (EqType tyAmbient' tL' tR') U1 maybeD' ->
                Just $ Identity !<$> AnalyzerInput tyAmbient' U1 (ClassifWillBe U1)
              otherwise -> Nothing
          )
          extCtxId
          (fmapCoe Identity)
          (AddressInfo ["ambient type"] False omit)
        rtL <- h Identity
          (\ gamma' -> \ case
              AnalyzerInput (EqType tyAmbient' tL' tR') U1 maybeD' ->
                Just $ Identity !<$> AnalyzerInput tL' U1 (ClassifMustBe tyAmbient')
              otherwise -> Nothing
          )
          extCtxId
          (fmapCoe Identity)
          (AddressInfo ["left equand"] False omit)
        rtR <- h Identity
          (\ gamma' -> \ case
              AnalyzerInput (EqType tyAmbient' tL' tR') U1 maybeD' ->
                Just $ Identity !<$> AnalyzerInput tR' U1 (ClassifMustBe tyAmbient')
              otherwise -> Nothing
          )
          extCtxId
          (fmapCoe Identity)
          (AddressInfo ["right equand"] False omit)
        return $ case token of
          TokenSubASTs ->
            Box1 $ runIdentity !<$> EqType (unbox1 rtyAmbient) (unbox1 rtL) (unbox1 rtR)
          TokenTypes -> BoxClassif $ dgamma
          TokenRelate -> Unit2

      SysType systy -> do
        rsysty <- h Identity
          (\ gamma' -> \ case
              AnalyzerInput (SysType systy') U1 maybeD' ->
                Just $ Identity !<$> AnalyzerInput systy' U1 (classifMust2will maybeD')
              otherwise -> Nothing
          )
          extCtxId
          (fmapCoe Identity)
          (AddressInfo ["system-specific type"] False EntirelyBoring)
        return $ case token of
          TokenSubASTs -> Box1 $ SysType $ runIdentity !<$> unbox1 rsysty
          TokenTypes -> BoxClassif $ runIdentity !<$> unboxClassif rsysty
          TokenRelate -> Unit2
        
    where handleBinder ::
            (forall w . Binding Type Type sys w -> UniHSConstructor sys w) ->
            Binding Type Type sys v ->
            (forall w . UniHSConstructor sys w -> Maybe (Binding Type Type sys w)) ->
            _ (AnalyzerResult option (UniHSConstructor sys) v)
          handleBinder binder binding extract = do
            rbinding <- h Identity
              (\ gamma' (AnalyzerInput ty' U1 maybeD') -> extract ty' <&> \ binding' ->
                  Identity !<$> AnalyzerInput binding' U1
                    (ClassifWillBe $ U1 :*: ClassifBinding (binding'segment binding') U1)
              )
              extCtxId
              (fmapCoe Identity)
              (AddressInfo ["binding"] False EntirelyBoring)
            return $ case token of
              TokenSubASTs -> Box1 $ binder $ runIdentity !<$> unbox1 rbinding
              TokenTypes -> BoxClassif $ unVarFromCtx <$> ctx'mode gamma
              TokenRelate -> Unit2
              
          handleConstant = pure $ case token of
            TokenSubASTs -> Box1 $ ty
            TokenTypes -> BoxClassif $ unVarFromCtx <$> ctx'mode gamma
            TokenRelate -> Unit2
            
  convRel token d = U1
  extraClassif = U1

-------------------------

instance SysAnalyzer sys => Analyzable sys (ConstructorTerm sys) where
  type Classif (ConstructorTerm sys) = Type sys
  type Relation (ConstructorTerm sys) = ModedDegree sys
  type AnalyzerExtraInput (ConstructorTerm sys) = U1
  analyzableToken = AnTokenConstructorTerm
  witClassif token = Witness
  analyze token gamma (AnalyzerInput t U1 _) h = Right $ do
    
    let dgamma' = ctx'mode gamma
    let dgamma = unVarFromCtx <$> dgamma'

    case t of

      ConsUniHS ty -> do
        rty <- h Identity
          (\ gamma' -> \ case
              AnalyzerInput (ConsUniHS ty') U1 _ ->
                Just $ Identity !<$> AnalyzerInput ty' U1 ClassifUnknown
              otherwise -> Nothing
          )
          extCtxId
          (fmapCoe Identity)
          (AddressInfo ["UniHS-constructor"] False EntirelyBoring)
        return $ case token of
          TokenSubASTs -> Box1 $ ConsUniHS $ runIdentity !<$> unbox1 rty
          TokenTypes -> BoxClassif $ hs2type $ UniHS $ runIdentity !<$> unboxClassif rty
          TokenRelate -> Unit2

      Lam binding -> do
        rbinding <- h Identity
          (\ gamma' -> \ case
              AnalyzerInput (Lam binding') U1 _ ->
                Just $ Identity !<$> AnalyzerInput binding' U1 ClassifUnknown
              otherwise -> Nothing
          )
          extCtxId
          (fmapCoe Identity)
          (AddressInfo ["binding"] False EntirelyBoring)
        return $ case token of
          TokenSubASTs -> Box1 $ Lam $ runIdentity !<$> unbox1 rbinding
          TokenTypes -> BoxClassif $ hs2type $ Pi $ Binding (binding'segment binding) $
            _classifBinding'body $ snd1 $ runIdentity !<$> unboxClassif rbinding
            --let (U1 :*: Comp1 ty) = unboxClassif rbinding
            --in  BoxClassif $ hs2type $ Pi $ Binding (binding'segment binding) ty
          TokenRelate -> Unit2

      Pair sigmaBinding tFst tSnd -> do
        rsigmaBinding <- h Identity
          (\ gamma' -> \ case
              AnalyzerInput (Pair sigmaBinding' tFst' tSnd') U1 _ ->
                Just $ Identity !<$> AnalyzerInput sigmaBinding' U1
                  (ClassifWillBe $ U1 :*: ClassifBinding (binding'segment sigmaBinding') U1)
              otherwise -> Nothing
          )
          extCtxId
          (fmapCoe Identity)
          (AddressInfo ["Sigma-type annotation"] False omit)
        rtFst <- h Identity
          (\ gamma' -> \ case
              AnalyzerInput (Pair sigmaBinding' tFst' tSnd') U1 _ ->
                Just $ Identity !<$> AnalyzerInput tFst' U1
                  (ClassifMustBe $ _segment'content $ binding'segment $ sigmaBinding')
              otherwise -> Nothing
          )
          extCtxId
          (fmapCoe Identity)
          (AddressInfo ["first component"] False omit)
        rtSnd <- h Identity
          (\ gamma' -> \ case
              AnalyzerInput (Pair sigmaBinding' tFst' tSnd') U1 _ ->
                Just $ Identity !<$> AnalyzerInput tSnd' U1
                  (ClassifMustBe $ substLast2 tFst' $ binding'body sigmaBinding')
              otherwise -> Nothing
          )
          extCtxId
          (fmapCoe Identity)
          (AddressInfo ["second component"] False omit)
        return $ case token of
          TokenSubASTs ->
            Box1 $ runIdentity !<$> Pair (unbox1 rsigmaBinding) (unbox1 rtFst) (unbox1 rtSnd)
          TokenTypes -> BoxClassif $ hs2type $ Sigma sigmaBinding
          TokenRelate -> Unit2

      ConsUnit -> pure $ case token of
        TokenSubASTs -> Box1 $ ConsUnit
        TokenTypes -> BoxClassif $ hs2type $ UnitType
        TokenRelate -> Unit2

      ConsBox boxSeg tUnbox -> do
        rboxSeg <- h Identity
          (\ gamma' -> \ case
              AnalyzerInput (ConsBox boxSeg' tUnbox') U1 _ ->
                Just $ Identity !<$> AnalyzerInput boxSeg' U1 (ClassifWillBe $ U1)
              otherwise -> Nothing
          )
          extCtxId
          (fmapCoe Identity)
          (AddressInfo ["Box-type annotation"] False omit)
        rtUnbox <- h Identity
          (\ gamma' -> \ case
              AnalyzerInput (ConsBox boxSeg' tUnbox') U1 _ ->
                Just $ Identity !<$> AnalyzerInput tUnbox' U1
                  (ClassifMustBe $ _segment'content boxSeg')
              otherwise -> Nothing
          )
          extCtxId
          (fmapCoe Identity)
          (AddressInfo ["box content"] False omit)
        return $ case token of
          TokenSubASTs -> Box1 $ runIdentity !<$> ConsBox (unbox1 rboxSeg) (unbox1 rtUnbox)
          TokenTypes -> BoxClassif $ hs2type $ BoxType boxSeg
          TokenRelate -> Unit2

      ConsZero -> pure $ case token of
        TokenSubASTs -> Box1 $ ConsZero
        TokenTypes -> BoxClassif $ hs2type $ NatType
        TokenRelate -> Unit2

      ConsSuc t -> do
        rt <- h Identity
          (\ gamma' -> \ case
              AnalyzerInput (ConsSuc t') U1 _ ->
                Just $ Identity !<$> AnalyzerInput t' U1 (ClassifMustBe $ hs2type NatType)
              otherwise -> Nothing
          )
          extCtxId
          (fmapCoe Identity)
          (AddressInfo ["predecessor"] False omit)
        return $ case token of
          TokenSubASTs -> Box1 $ ConsSuc $ runIdentity !<$> (unbox1 rt)
          TokenTypes -> BoxClassif $ hs2type $ NatType
          TokenRelate -> Unit2

      ConsRefl tyAmbient t -> do
        rtyAmbient <- h Identity
          (\ gamma' -> \ case
              AnalyzerInput (ConsRefl tyAmbient' t') U1 _ ->
                Just $ Identity !<$> AnalyzerInput tyAmbient' U1 (ClassifWillBe U1)
              otherwise -> Nothing
          )
          extCtxId
          (fmapCoe Identity)
          (AddressInfo ["ambient type"] False omit)
        rt <- h Identity
          (\ gamma' -> \ case
              AnalyzerInput (ConsRefl tyAmbient' t') U1 _ ->
                Just $ Identity !<$> AnalyzerInput t' U1 ClassifUnknown
              otherwise -> Nothing
          )
          extCtxId
          (fmapCoe Identity)
          (AddressInfo ["self-equand"] False omit)
        return $ case token of
          TokenSubASTs -> Box1 $ runIdentity !<$> ConsRefl (unbox1 rtyAmbient) (unbox1 rt)
          TokenTypes -> BoxClassif $ hs2type $ EqType (runIdentity !<$> unboxClassif rt) t t
          TokenRelate -> Unit2

  convRel token d = modedEqDeg d
  extraClassif = U1

-------------------------

instance SysAnalyzer sys => Analyzable sys (Type sys) where
  type Classif (Type sys) = U1
  type Relation (Type sys) = ModedDegree sys
  type AnalyzerExtraInput (Type sys) = U1
  analyzableToken = AnTokenType
  witClassif token = Witness
  analyze token gamma (AnalyzerInput (Type t) U1 maybeU1) h = Right $ do
    rt <- h Identity
      (\ gamma' (AnalyzerInput (Type t') U1 maybeU1') ->
         Just $ Identity !<$> AnalyzerInput t' U1
           (ClassifMustBe $ hs2type $ UniHS $ unVarFromCtx <$> ctx'mode gamma'))
      extCtxId
      (fmapCoe Identity)
      (AddressInfo ["code"] True WorthMentioning)
    return $ case token of
      TokenSubASTs -> Box1 $ Type $ runIdentity !<$> unbox1 rt
      TokenTypes -> BoxClassif U1
      TokenRelate -> Unit2
    
  convRel token gamma = U1
  extraClassif = U1

-------------------------

instance SysAnalyzer sys => Analyzable sys (DependentEliminator sys) where
  type Classif (DependentEliminator sys) = U1
  type Relation (DependentEliminator sys) = ModedDegree sys
  type AnalyzerExtraInput (DependentEliminator sys) =
    ModedModality sys :*: Term sys :*: UniHSConstructor sys :*: (Type sys :.: VarExt)
  analyzableToken = AnTokenDependentEliminator
  witClassif token = Witness

  analyze token gamma
    (AnalyzerInput clauses
      (dmuElim :*: eliminee :*: tyEliminee :*: Comp1 (motive :: Type sys (VarExt v)))
      maybeU1)
    h
    = Right $ do

    let dgamma' = ctx'mode gamma
    let dgamma = unVarFromCtx <$> dgamma'

    case (tyEliminee, clauses) of
      
      (Sigma binding, ElimSigma boundBoundPairClause) -> do
        rboundBoundPairClause <- h Identity
          (\ (gamma' :: Ctx _ _ u Void)
             (AnalyzerInput clauses'
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
                 in  Just $ Identity !<$> AnalyzerInput
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
          TokenSubASTs -> Box1 $ ElimSigma $ runIdentity !<$> unbox1 rboundBoundPairClause
          TokenTypes -> BoxClassif U1
          TokenRelate -> Unit2
      (_, ElimSigma _) -> unreachable

      (BoxType seg, ElimBox boundBoxClause) -> do
        rboundBoxClause <- h Identity
          (\ (gamma' :: Ctx _ _ u Void)
             (AnalyzerInput clauses'
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
                 in  Just $ Identity !<$> AnalyzerInput
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
          TokenSubASTs -> Box1 $ ElimBox $ runIdentity !<$> unbox1 rboundBoxClause
          TokenTypes -> BoxClassif U1
          TokenRelate -> Unit2
      (_, ElimBox _) -> unreachable

      (EmptyType, ElimEmpty) -> pure $ case token of
        TokenSubASTs -> Box1 ElimEmpty
        TokenTypes -> BoxClassif U1
        TokenRelate -> Unit2
      (_, ElimEmpty) -> unreachable
      
      (NatType, ElimNat (zeroClause :: Term sys v) boundBoundSucClause) -> do
        rzeroClause <- h Identity
          (\ (gamma' :: Ctx _ _ u Void)
             (AnalyzerInput clauses'
               (dmuElim' :*: eliminee' :*: tyEliminee' :*: Comp1 (motive' :: Type sys (VarExt u)))
               maybeU1'
             ) -> case (tyEliminee', clauses') of
               (NatType, ElimNat zeroClause' boundBoundSucClause') ->
                 Just $ Identity !<$> AnalyzerInput zeroClause' U1
                 (ClassifMustBe $ substLast2 (Expr2 $ TermCons $ ConsZero :: Term sys u) $ motive')
               otherwise -> Nothing
          )
          extCtxId
          (fmapCoe Identity)
          (AddressInfo ["zero clause"] False omit)
        rboundBoundSucClause <- h Identity
          (\ (gamma' :: Ctx _ _ u Void)
             (AnalyzerInput clauses'
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
                 in  Just $ Identity !<$> AnalyzerInput
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
          TokenSubASTs ->
            Box1 $ runIdentity !<$> ElimNat (unbox1 rzeroClause) (unbox1 rboundBoundSucClause)
          TokenTypes -> BoxClassif U1
          TokenRelate -> Unit2
      (_, ElimNat _ _) -> unreachable

  convRel token gamma = U1
  extraClassif = U1

-------------------------

instance SysAnalyzer sys => Analyzable sys (Eliminator sys) where
  type Classif (Eliminator sys) = Type sys
  type Relation (Eliminator sys) = ModedDegree sys
  type AnalyzerExtraInput (Eliminator sys) = ModedModality sys :*: Term sys :*: UniHSConstructor sys
  analyzableToken = AnTokenEliminator
  witClassif token = Witness

  analyze token gamma (AnalyzerInput eliminator (dmuElim :*: eliminee :*: tyEliminee) _) h =
    Right $ do

    let dgamma' = ctx'mode gamma
    let dgamma = unVarFromCtx <$> dgamma'

    case (tyEliminee, eliminator) of

      (Pi binding, App arg) -> do
        rarg <- h Identity
          (\ gamma' (AnalyzerInput eliminator' (dmuElim' :*: eliminee' :*: tyEliminee') _) ->
             case (tyEliminee', eliminator') of
               (Pi binding', App arg') ->
                 Just $ Identity !<$> AnalyzerInput arg' U1
                 (ClassifMustBe $ _segment'content $ binding'segment binding')
               otherwise -> Nothing
          )
          (\ gamma' (AnalyzerInput eliminator' (dmuElim' :*: eliminee' :*: tyEliminee') _) _ ->
             case (tyEliminee', eliminator') of
               (Pi binding', App arg') ->
                 Just $ CtxId $ VarFromCtx <$> _segment'modty (binding'segment binding') :\\ gamma'
               otherwise -> Nothing
          )
          (fmapCoe Identity . modedDivDeg (_segment'modty $ binding'segment binding))
          (AddressInfo ["argument"] False omit)
        return $ case token of
          TokenSubASTs -> Box1 $ App $ runIdentity !<$> unbox1 rarg
          TokenTypes -> BoxClassif $ substLast2 arg $ binding'body binding
          TokenRelate -> Unit2
      (_, App arg) -> unreachable

      (Sigma binding, Fst) -> pure $ case token of
          TokenSubASTs -> Box1 $ Fst
          TokenTypes -> BoxClassif $ _segment'content $ binding'segment binding
          TokenRelate -> Unit2
      (_, Fst) -> unreachable

      (Sigma binding, Snd) -> pure $ case token of
        TokenSubASTs -> Box1 $ Snd
        TokenTypes -> BoxClassif $
          substLast2 (Expr2 $
            TermElim
              (modedApproxLeftAdjointProj $ _segment'modty $ binding'segment binding)
              eliminee
              (Sigma binding)
              Fst
            ) $
          binding'body binding
        TokenRelate -> Unit2
      (_, Snd) -> unreachable

      (BoxType seg, Unbox) -> pure $ case token of
        TokenSubASTs -> Box1 $ Unbox
        TokenTypes -> BoxClassif $ _segment'content seg
        TokenRelate -> Unit2
      (_, Unbox) -> unreachable

      (Pi binding, Funext) -> pure $ case token of
        TokenSubASTs -> Box1 $ Funext
        TokenTypes -> case binding'body binding of
          TypeHS (EqType tyAmbient tL tR) -> BoxClassif $ hs2type $ EqType
            (hs2type $ Pi $           Binding (binding'segment binding) tyAmbient)
            (Expr2 $ TermCons $ Lam $ Binding (binding'segment binding) tL)
            (Expr2 $ TermCons $ Lam $ Binding (binding'segment binding) tR)
          _ -> unreachable
        TokenRelate -> Unit2
      (_, Funext) -> unreachable

      (_, ElimDep boundMotive@(NamedBinding name motive) clauses) -> do
        rboundMotive <- h Identity
          (\ gamma' (AnalyzerInput eliminator' (dmuElim' :*: eliminee' :*: tyEliminee') _) ->
             case (tyEliminee', eliminator') of
               (_, ElimDep boundMotive' clauses') ->
                 let seg' = Declaration (DeclNameSegment Nothing) dmuElim' Explicit
                       (hs2type tyEliminee')
                 in  Just $ Identity !<$> AnalyzerInput boundMotive'
                       (seg' :*: Comp1 U1)
                       (ClassifWillBe $ ClassifBinding seg' U1)
               otherwise -> Nothing
          )
          extCtxId
          (Comp1 . fmap (VarWkn . Identity))
          (AddressInfo ["motive"] False omit)
        rclauses <- h Identity
          (\ gamma' (AnalyzerInput eliminator' (dmuElim' :*: eliminee' :*: tyEliminee') _) ->
             case (tyEliminee', eliminator') of
               (_, ElimDep (NamedBinding name' motive') clauses') ->
                 Just $ Identity !<$> AnalyzerInput clauses'
                       (dmuElim' :*: eliminee' :*: tyEliminee' :*: Comp1 motive')
                       (ClassifWillBe U1)
               otherwise -> Nothing
          )
          extCtxId
          (fmapCoe Identity)
          (AddressInfo ["clauses"] False EntirelyBoring)
        return $ case token of
          TokenSubASTs ->
            Box1 $ runIdentity !<$> ElimDep (unbox1 rboundMotive) (unbox1 rclauses)
          TokenTypes -> BoxClassif $ substLast2 eliminee motive
          TokenRelate -> Unit2
          
      (EqType tyAmbient tL tR, ElimEq boundBoundMotive clauseRefl) -> do
        rboundBoundMotive <- h Identity
          (\ gamma' (AnalyzerInput eliminator' (dmuElim' :*: eliminee' :*: tyEliminee') _) ->
             case (tyEliminee', eliminator') of
               (EqType tyAmbient' tL' tR', ElimEq boundBoundMotive' clauseRefl') ->
                 let segR' = Declaration (DeclNameSegment Nothing) dmuElim' Explicit tyAmbient'
                     segEq' = Declaration
                       (DeclNameSegment Nothing)
                       (VarWkn <$> dmuElim')
                       Explicit
                       (hs2type $ EqType (VarWkn <$> tyAmbient') (VarWkn <$> tL') (Var2 VarLast))
                 in  Just $ Identity !<$> AnalyzerInput boundBoundMotive'
                       (segR' :*: Comp1 (segEq' :*: Comp1 U1))
                       (ClassifWillBe $ ClassifBinding segR' $ ClassifBinding segEq' $ U1)
               otherwise -> Nothing
          )
          extCtxId
          (Comp1 . Comp1 . fmap (VarWkn . VarWkn . Identity))
          (AddressInfo ["motive"] False omit)
        rclauseRefl <- h Identity
          (\ gamma' (AnalyzerInput eliminator' (dmuElim' :*: eliminee' :*: tyEliminee') _) ->
             case (tyEliminee', eliminator') of
               (EqType tyAmbient' tL' tR', ElimEq boundBoundMotive' clauseRefl') ->
                 Just $ Identity !<$> AnalyzerInput clauseRefl' U1
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
           TokenSubASTs ->
             Box1 $ runIdentity !<$> ElimEq (unbox1 rboundBoundMotive) (unbox1 rclauseRefl)
           TokenTypes -> BoxClassif $ substLast2 tR $ substLast2 (VarWkn <$> eliminee) $
             _namedBinding'body $ _namedBinding'body $ boundBoundMotive
           TokenRelate -> Unit2
      (_, ElimEq _ _) -> unreachable

  convRel token d = modedEqDeg d
  extraClassif = U1

-------------------------

instance SysAnalyzer sys => Analyzable sys (TermNV sys) where
  type Classif (TermNV sys) = Type sys
  type Relation (TermNV sys) = ModedDegree sys
  type AnalyzerExtraInput (TermNV sys) = U1
  analyzableToken = AnTokenTermNV
  witClassif token = Witness

  analyze token gamma (AnalyzerInput t U1 maybeTy) h = case t of

    TermCons c -> Right $ do
      rc <- h Identity
        (\ gamma' -> \ case
            (AnalyzerInput (TermCons c') U1 maybeTy') ->
              Just $ Identity !<$> AnalyzerInput c' U1 (classifMust2will maybeTy')
            otherwise -> Nothing
        )
        extCtxId
        (fmapCoe Identity)
        (AddressInfo ["underlying constructor"] False EntirelyBoring)
      return $ case token of
        TokenSubASTs -> Box1 $ TermCons $ runIdentity !<$> unbox1 rc
        TokenTypes -> BoxClassif $ runIdentity !<$> unboxClassif rc
        TokenRelate -> Unit2

    TermElim dmuElim eliminee tyEliminee eliminator -> Right $ do
      rdmuElim <- h Identity
        (\ gamma' -> \ case
            (AnalyzerInput (TermElim dmuElim' eliminee' tyEliminee' eliminator') U1 maybeTy') ->
              Just $ Identity !<$> AnalyzerInput dmuElim' U1
                (ClassifMustBe $ modality'dom dmuElim' :*: (unVarFromCtx <$> ctx'mode gamma'))
            otherwise -> Nothing
        )
        extCtxId
        (const $ Const ModEq)
        (AddressInfo ["modality of elimination"] False omit)
      reliminee <- h Identity
        (\ gamma' -> \ case
            (AnalyzerInput (TermElim dmuElim' eliminee' tyEliminee' eliminator') U1 maybeTy') ->
              Just $ Identity !<$> AnalyzerInput eliminee' U1 (ClassifMustBe $ hs2type tyEliminee')
            otherwise -> Nothing
        )
        (\ gamma' input1 condInput2 -> case input1 of
            (AnalyzerInput (TermElim dmuElim' eliminee' tyEliminee' eliminator') U1 maybeTy') ->
              Just $ CtxId $ VarFromCtx <$> dmuElim' :\\ gamma'
            otherwise -> Nothing
        )
        (fmapCoe Identity . modedDivDeg dmuElim)
        (AddressInfo ["eliminee"] True omit)
      rtyEliminee <- h Identity
        (\ gamma' -> \ case
            (AnalyzerInput (TermElim dmuElim' eliminee' tyEliminee' eliminator') U1 maybeTy') ->
              Just $ Identity !<$> AnalyzerInput tyEliminee' U1 (ClassifMustBe $ unVarFromCtx <$> ctx'mode gamma')
            otherwise -> Nothing
        )
        (\ gamma' input1 condInput2 -> case input1 of
            (AnalyzerInput (TermElim dmuElim' eliminee' tyEliminee' eliminator') U1 maybeTy') ->
              Just $ CtxId $ VarFromCtx <$> dmuElim' :\\ gamma'
            otherwise -> Nothing
        )
        (fmapCoe Identity . modedDivDeg dmuElim)
        (AddressInfo ["type of eliminee"] False omit)
      reliminator <- h Identity
        (\ gamma' -> \ case
            (AnalyzerInput (TermElim dmuElim' eliminee' tyEliminee' eliminator') U1 maybeTy') ->
              Just $ Identity !<$> AnalyzerInput
                eliminator'
                (dmuElim' :*: eliminee' :*: tyEliminee')
                ClassifUnknown
            otherwise -> Nothing
        )
        extCtxId
        (fmapCoe Identity)
        (AddressInfo ["eliminator"] False EntirelyBoring)
      return $ case token of
        TokenSubASTs ->
          Box1 $ runIdentity !<$> TermElim (unbox1 rdmuElim) (unbox1 reliminee) (unbox1 rtyEliminee) (unbox1 reliminator)
        TokenTypes -> BoxClassif $ runIdentity !<$> unboxClassif reliminator
        TokenRelate -> Unit2

    TermMeta _ _ _ _ -> Left AnErrorTermMeta

    TermWildcard -> Left AnErrorTermWildcard

    TermQName _ _ -> Left AnErrorTermQName

    TermAlreadyChecked t ty -> Left AnErrorTermAlreadyChecked
      {-Just $ do
      rt <- h id gamma (AnalyzerInput t U1 (Just ty) maybeRel)
      rty <- h id gamma (AnalyzerInput ty U1 (Just U1) maybeRel)
      return $ case token of
        TokenSubASTs -> Box1 $ -}

    TermAlgorithm _ _ -> Left AnErrorTermAlgorithm

    TermSys syst -> Right $ do
      rsyst <- h Identity
        (\ gamma' -> \ case
            (AnalyzerInput (TermSys syst') U1 maybeTy') ->
              Just $ Identity !<$> AnalyzerInput syst' U1 (classifMust2will maybeTy')
            otherwise -> Nothing
        )
        extCtxId
        (fmapCoe Identity)
        (AddressInfo ["system-specific term"] True EntirelyBoring)
      return $ case token of
        TokenSubASTs -> Box1 $ TermSys $ runIdentity !<$> unbox1 rsyst
        TokenTypes -> BoxClassif $ runIdentity !<$> unboxClassif rsyst
        TokenRelate -> Unit2

    TermProblem t -> Left AnErrorTermProblem
    
  convRel token d = modedEqDeg d
  extraClassif = U1

-------------------------

instance SysAnalyzer sys => Analyzable sys (Term sys) where
  type Classif (Term sys) = Type sys
  type Relation (Term sys) = ModedDegree sys
  type AnalyzerExtraInput (Term sys) = U1
  analyzableToken = AnTokenTerm
  witClassif token = Witness
  analyze token gamma (AnalyzerInput t U1 maybeTy) h = case t of
    Expr2 tnv -> Right $ do
      rtnv <- h Identity
        (\ gamma' -> \ case
            (AnalyzerInput (Expr2 tnv') U1 maybeTy') ->
              Just $ Identity !<$> AnalyzerInput tnv' U1 (classifMust2will maybeTy')
            otherwise -> Nothing
        )
        extCtxId
        (fmapCoe Identity)
        (AddressInfo ["non-variable"] True EntirelyBoring)
      return $ case token of
        TokenSubASTs -> Box1 $ Expr2 $ runIdentity !<$> unbox1 rtnv
        TokenTypes -> BoxClassif $ runIdentity !<$> unboxClassif rtnv
        TokenRelate -> Unit2
    Var2 v -> Left AnErrorVar
  convRel token d = modedEqDeg d
  extraClassif = U1

-------------------------

instance (SysAnalyzer sys, Analyzable sys (rhs sys)) => Analyzable sys (Declaration declSort rhs sys) where
  type Classif (Declaration declSort rhs sys) = Classif (rhs sys)
  type Relation (Declaration declSort rhs sys) = Relation (rhs sys)
  type AnalyzerExtraInput (Declaration declSort rhs sys) = AnalyzerExtraInput (rhs sys)
  analyzableToken = AnTokenDeclaration analyzableToken
  witClassif token = haveClassif @sys @(rhs sys) Witness
  {-
  analyze token fromType gamma (AnalyzerInput seg@(Declaration name dmu plic ty) extra maybeTy maybeRel) h = Right $ do
    let dgamma' = ctx'mode gamma
    let dgamma = unVarFromCtx <$> dgamma'
    
    rdmu <- h id (crispModedModality dgamma' :\\ gamma)
      (AnalyzerInput dmu U1 (ClassifMustBe $ modality'dom dmu :*: dgamma) (toIfRelate token $ Const ModEq))
      (AddressInfo ["modality"] True omit)
      (Just . _decl'modty)
    -- TODO plic
    rty <- h id (VarFromCtx <$> dmu :\\ gamma)
      (AnalyzerInput ty extra (classifMust2will maybeTy) maybeRel)
      (AddressInfo ["type"] True omit)
      (Just . _decl'content)

    return $ case token of
      TokenSubASTs -> Box1 $ Declaration name (unbox1 rdmu) plic (unbox1 rty)
      TokenTypes -> BoxClassif $ unboxClassif rty
      TokenRelate -> Unit2
-}
  convRel token d = convRel (analyzableToken @sys @(rhs sys)) d
  extraClassif = extraClassif @sys @(rhs sys)

-------------------------

instance (SysAnalyzer sys,
          Analyzable sys (rhs sys),
          Classif (rhs sys) ~ U1,
          AnalyzerExtraInput (rhs sys) ~ U1) => Analyzable sys (Telescoped Type rhs sys) where
  type Classif (Telescoped Type rhs sys) = U1
  type Relation (Telescoped Type rhs sys) = Relation (Type sys) :*: Relation (rhs sys)
  type AnalyzerExtraInput (Telescoped Type rhs sys) = U1
  analyzableToken = AnTokenTelescoped analyzableToken
  witClassif token = Witness
  {-
  analyze token fromType gamma (AnalyzerInput telescopedRHS U1 maybeU1 maybeRels) h = Right $ do

    let dgamma' = ctx'mode gamma
    let dgamma = unVarFromCtx <$> dgamma'

    case telescopedRHS of
      Telescoped rhs -> do
        rrhs <- h id gamma (AnalyzerInput rhs U1 (ClassifWillBe U1) (snd1 <$> maybeRels))
          (AddressInfo ["rhs"] True omit)
          $ \case
            Telescoped rhs -> Just rhs
            _ -> Nothing
        return $ case token of
          TokenSubASTs -> Box1 $ Telescoped $ unbox1 rrhs
          TokenTypes -> BoxClassif U1
          TokenRelate -> Unit2
      seg :|- telescopedRHS -> do
        rseg <- h id gamma (AnalyzerInput seg U1 (ClassifWillBe U1) (fst1 <$> maybeRels))
          (AddressInfo ["a segment"] True omit)
          $ \case
            seg :|- telescopedRHS -> Just seg
            _ -> Nothing
        rtelescopedRHS <- fromRight unreachable $
          analyze token fromType
            (gamma :.. VarFromCtx <$> (decl'content %~ fromType) seg)
            (AnalyzerInput telescopedRHS U1 (ClassifWillBe U1) (fmap VarWkn <$> maybeRels))
            (\ wkn gammadelta input info extract -> h (wkn . VarWkn) gammadelta input info $ \case
                seg :|- telescopedRHS -> extract telescopedRHS
                _ -> Nothing
            )
        return $ case token of
          TokenSubASTs -> Box1 $ unbox1 rseg :|- unbox1 rtelescopedRHS
          TokenTypes -> BoxClassif U1
          TokenRelate -> Unit2
      dmu :** telescopedRHS -> do
        rdmu <- h id (crispModedModality dgamma' :\\ gamma)
          (AnalyzerInput dmu U1 (ClassifMustBe $ modality'dom dmu :*: dgamma) (toIfRelate token $ Const ModEq))
          (AddressInfo ["applied modality"] True omit)
          $ \case
            dmu :** telescopedRHS -> Just dmu
            _ -> Nothing
        rtelescopedRHS <- fromRight unreachable $
          analyze token fromType
            (VarFromCtx <$> dmu :\\ gamma)
            (AnalyzerInput telescopedRHS U1 (ClassifWillBe U1) maybeRels)
            (\ wkn gammadelta input info extract -> h wkn gammadelta input info $ \case
                dmu :** telescopedRHS -> extract telescopedRHS
                _ -> Nothing
            )
        return $ case token of
          TokenSubASTs -> Box1 $ unbox1 rdmu :** unbox1 rtelescopedRHS
          TokenTypes -> BoxClassif U1
          TokenRelate -> Unit2
-}
  convRel token d = U1
  extraClassif = U1

-------------------------

instance SysAnalyzer sys => Analyzable sys (ValRHS sys) where
  type Classif (ValRHS sys) = U1
  type Relation (ValRHS sys) = ModedDegree sys
  type AnalyzerExtraInput (ValRHS sys) = U1
  analyzableToken = AnTokenValRHS
  witClassif token = Witness
  {-
  analyze token fromType gamma (AnalyzerInput valRHS@(ValRHS t ty) U1 maybeU1 maybeRel) h = Right $ do
    rt <- h id gamma (AnalyzerInput t U1 (ClassifMustBe ty) maybeRel) (AddressInfo ["RHS"] True omit) (Just . _val'term)
    rty <- h id gamma (AnalyzerInput ty U1 (ClassifWillBe U1) maybeRel) (AddressInfo ["type"] True omit) (Just . _val'type)
    return $ case token of
      TokenSubASTs -> Box1 $ ValRHS (unbox1 rt) (unbox1 rty)
      TokenTypes -> BoxClassif $ U1
      TokenRelate -> Unit2
-}
  convRel token d = U1
  extraClassif = U1

-------------------------

instance SysAnalyzer sys => Analyzable sys (ModuleRHS sys) where
  type Classif (ModuleRHS sys) = U1
  type Relation (ModuleRHS sys) = ModedDegree sys
  type AnalyzerExtraInput (ModuleRHS sys) = U1
  analyzableToken = AnTokenModuleRHS
  witClassif token = Witness
  {-
  analyze token fromType gamma (AnalyzerInput moduleRHS@(ModuleRHS (Compose revEntries)) U1 maybeU1 maybeRel) h = Right $ do
    rcontent <- sequenceA $ zip (reverse revEntries) (reverse $ tails revEntries) <&> \ (entry, revPrevEntries) ->
      h VarInModule (gamma :<...> VarFromCtx <$> ModuleRHS (Compose $ revPrevEntries))
        (AnalyzerInput entry U1 (ClassifWillBe U1) (fmap VarInModule <$> maybeRel))
        (AddressInfo ["an entry"] True omit)
        (const Nothing) -- Relatedness of modules is never of interest.
    return $ case token of
      TokenSubASTs -> Box1 $ ModuleRHS $ Compose $ unbox1 <$> rcontent
      TokenTypes -> BoxClassif $ U1
      TokenRelate -> Unit2
-}
  convRel token d = U1
  extraClassif = U1

-------------------------

{-
instance SysAnalyzer sys => Analyzable (Val sys) where
  type Classif (Val sys) = U1
  type Relation (Val sys) = ModedDegree sys
  type AnalyzerExtraInput (Val sys) = U1
  analyze token fromType h gamma (AnalyzerInput val@(Declaration ))
-}

------------------------

instance SysAnalyzer sys => Analyzable sys (Entry sys) where
  type Classif (Entry sys) = U1
  type Relation (Entry sys) = ModedDegree sys
  type AnalyzerExtraInput (Entry sys) = U1
  analyzableToken = AnTokenEntry
  witClassif token = Witness
  {-
  analyze token fromType gamma (AnalyzerInput entry U1 maybeU1 maybeRel) h = Right $ do
    case entry of
      EntryVal val -> do
        rval <- h id gamma
          (AnalyzerInput val U1 (ClassifWillBe U1) ((\ x -> x :*: x) <$> maybeRel))
          (AddressInfo ["val"] True EntirelyBoring)
          $ \case
            EntryVal val -> Just val
            EntryModule modul -> Nothing
        return $ case token of
          TokenSubASTs -> Box1 $ EntryVal $ unbox1 rval
          TokenTypes -> BoxClassif $ U1
          TokenRelate -> Unit2
      EntryModule modul -> do
        rmodul <- h id gamma
          (AnalyzerInput modul U1 (ClassifWillBe U1) ((\ x -> x :*: x) <$> maybeRel))
          (AddressInfo ["module"] True EntirelyBoring)
          $ \case
            EntryVal val -> Nothing
            EntryModule modul -> Just modul
        return $ case token of
          TokenSubASTs -> Box1 $ EntryModule $ unbox1 rmodul
          TokenTypes -> BoxClassif $ U1
          TokenRelate -> Unit2
-}
  convRel token d = U1
  extraClassif = U1

------------------------
------------------------

instance (SysAnalyzer sys) => Analyzable sys U1 where
  type Classif U1 = U1
  type Relation U1 = U1
  type AnalyzerExtraInput U1 = U1
  analyzableToken = AnTokenU1
  witClassif token = Witness
  {-
  analyze token fromType gamma (AnalyzerInput U1 U1 _ _) h =
    Right $ pure $ case token of
        TokenSubASTs -> Box1 $ U1
        TokenTypes -> BoxClassif $ U1
        TokenRelate -> Unit2
-}
  convRel token d = U1
  extraClassif = U1

------------------------

instance (SysAnalyzer sys,
          Analyzable sys f,
          Analyzable sys g) => Analyzable sys (f :*: g) where
  type Classif (f :*: g) = Classif f :*: Classif g
  type Relation (f :*: g) = Relation f :*: Relation g
  type AnalyzerExtraInput (f :*: g) = AnalyzerExtraInput f :*: AnalyzerExtraInput g
  analyzableToken = AnTokenPair1 analyzableToken analyzableToken
  witClassif token = 
    haveClassif @sys @f $
    haveClassif @sys @g $ Witness
    {-
  analyze token fromType gamma (AnalyzerInput (fv :*: gv) (extraF :*: extraG) maybeClassifs maybeRels) h = Right $ do
    rfv <- h id gamma
      (AnalyzerInput fv extraF (fst1 <$> maybeClassifs) (fst1 <$> maybeRels))
      (AddressInfo ["first component"] True omit)
      (Just . fst1)
    rgv <- h id gamma
      (AnalyzerInput gv extraG (snd1 <$> maybeClassifs) (snd1 <$> maybeRels))
      (AddressInfo ["second component"] True omit)
      (Just . snd1)
    return $ case token of
      TokenSubASTs -> Box1 $ unbox1 rfv :*: unbox1 rgv
      TokenTypes -> BoxClassif $ unboxClassif rfv :*: unboxClassif rgv
      TokenRelate -> Unit2
-}
  convRel token d = convRel (analyzableToken @sys @f) d :*:
                    convRel (analyzableToken @sys @g) d
  extraClassif = extraClassif @sys @f :*:
                 extraClassif @sys @g
      
    {-
    analyzeF <-
      analyze token fromType h gamma (AnalyzerInput fv extraF (fst1 <$> classifMust2will maybeClassifs) (fst1 <$> maybeRels))
    analyzeG <-
      analyze token fromType h gamma (AnalyzerInput gv extraG (snd1 <$> classifMust2will maybeClassifs) (snd1 <$> maybeRels))
    return $ do
      rfv <- analyzeF
      rgv <- analyzeG
      return $ case token of
        TokenSubASTs -> Box1 $ unbox1 rfv :*: unbox1 rgv
        TokenTypes -> BoxClassif $ unboxClassif rfv :*: unboxClassif rgv
        TokenRelate -> Unit2
    -}

------------------------

{-
instance (SysAnalyzer sys,
          Analyzable sys t,
          Analyzable sys (Classif t),
          Applicative f) => Analyzable sys (Compose f t) where
  type Classif (Compose f t) = Classif t
  type Relation (Compose f t) = Relation t
  type AnalyzerExtraInput (Compose f t) = Compose f (AnalyzerExtraInput t)
  analyzableToken = AnTokenCompose analyzableToken
  analyze token fromType gamma (AnalyzerInput (Compose ftv) (Compose fextra) maybeClassifs maybeRel) h = Right $ do
    return $ case token of
      TokenSubASTs -> 
-}

------------------------

{-
instance (SysAnalyzer sys,
          Analyzable sys f,
          Functor g) => Analyzable sys (f :.: g) where
  type Classif (f :.: g) = Classif f :.: g
  type Relation (f :.: g) = Relation f :.: g
  type AnalyzerExtraInput (f :.: g) = AnalyzerExtraInput f :.: g
  analyze token fromType h gamma (AnalyzerInput (Comp1 fgv) (Comp1 extra) maybeCompClassif maybeCompRel) = do
    analyze <- analyze token fromType _h gamma
      (AnalyzerInput fgv extra (unComp1 <$> maybeCompClassif) (unComp1 <$> maybeCompRel))
    return $ do
      rfgv <- analyze
      return $ case token of
        TokenSubASTs -> Box1 $ Comp1 $ unbox1 rfgv
        TokenTypes -> BoxClassif $ Comp1 $ unboxClassif rfgv
        TokenRelate -> Unit2
-}

------------------------
        
-- INSTEAD OF USING :.:, USE ClassifBinding, WHICH DOES NOT COMPARE SEGMENTS
