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

import GHC.Generics
import Data.Functor.Const
import Control.Lens
import Data.Functor.Compose
import Control.Monad
import Data.Void
import Data.Maybe

-------------------------

instance (SysAnalyzer sys) => Analyzable sys (ModedModality sys) where
  type Classif (ModedModality sys) = Mode sys :*: Mode sys -- domain and codomain
  type Relation (ModedModality sys) = Const ModRel
  type AnalyzerExtraInput (ModedModality sys) = U1
  analyze token fromType h gamma (AnalyzerInput (ModedModality ddom dcod mu) U1 _ maybeRel) = Just $ do
    rddom <- h id gamma (AnalyzerInput ddom U1 (Just U1) (toIfRelate token U1)) (AddressInfo ["domain"] True omit)
    rdcod <- h id gamma (AnalyzerInput dcod U1 (Just U1) (toIfRelate token U1)) (AddressInfo ["codomain"] True omit)
    rmu   <- h id gamma (AnalyzerInput mu U1 (Just $ ddom :*: dcod) maybeRel) (AddressInfo ["modality"] True omit)
    return $ case token of
        TokenSubterms -> Box1 $ ModedModality (unbox1 rddom) (unbox1 rdcod) (unbox1 rmu)
        TokenTypes -> BoxClassif $ ddom :*: dcod
        TokenRelate -> Unit2

-------------------------

instance (SysAnalyzer sys,
          Analyzable sys (rhs sys),
          Relation (rhs sys) ~ ModedDegree sys,
          AnalyzerExtraInput (rhs sys) ~ U1
         ) => Analyzable sys (Binding Type rhs sys) where
  type Classif (Binding Type rhs sys) = Classif (Segment Type sys) :*: (Classif (rhs sys) :.: VarExt)
  type Relation (Binding Type rhs sys) = ModedDegree sys
  type AnalyzerExtraInput (Binding Type rhs sys) = U1
  analyze token fromType h gamma (AnalyzerInput (Binding seg body) U1 maybeCl maybeDDeg) = Just $ do
    rseg <- h id gamma
      (AnalyzerInput seg U1 (fst1 <$> maybeCl) maybeDDeg)
      (AddressInfo ["segment"] False omit)
    rbody <- h VarWkn (gamma :.. VarFromCtx <$> (decl'content %~ fromType) seg)
      (AnalyzerInput body U1 (unComp1 . snd1 <$> maybeCl) (fmap VarWkn <$> maybeDDeg))
      (AddressInfo ["body"] False omit)
    return $ case token of
      TokenSubterms -> Box1 $ Binding (unbox1 rseg) (unbox1 rbody)
      TokenTypes -> BoxClassif $ unboxClassif rseg :*: Comp1 (unboxClassif rbody)
      TokenRelate -> Unit2

-------------------------

instance (SysAnalyzer sys) => Analyzable sys (UniHSConstructor sys) where
  
  type Classif (UniHSConstructor sys) = Compose Maybe (Mode sys) -- a mode if you care
  type Relation (UniHSConstructor sys) = ModedDegree sys
  type AnalyzerExtraInput (UniHSConstructor sys) = U1
  
  analyze (token :: AnalyzerToken option) fromType h
    (gamma :: Ctx lhs sys v Void) (AnalyzerInput ty U1 maybeMaybeD maybeDDeg) = Just $ do
    
    let dgamma' = ctx'mode gamma
    let dgamma = unVarFromCtx <$> dgamma'

    case ty of
      
      UniHS d -> do
        rd <- h id (crispModedModality dgamma' :\\ gamma)
          (AnalyzerInput d U1 (Just U1) (toIfRelate token U1))
          (AddressInfo ["mode"] False omit)
        return $ case token of
          TokenSubterms -> Box1 $ UniHS (unbox1 rd)
          TokenTypes -> BoxClassif $ Compose $ Just $ d
          TokenRelate -> Unit2

      Pi binding -> handleBinder Pi binding

      Sigma binding -> handleBinder Sigma binding

      EmptyType -> handleConstant

      UnitType -> handleConstant

      BoxType segment -> do
        rsegment <- h id gamma (AnalyzerInput segment U1 (Just U1) maybeDDeg)
          (AddressInfo ["segment"] False EntirelyBoring)
        return $ case token of
          TokenSubterms -> Box1 $ BoxType $ unbox1 rsegment
          TokenTypes -> BoxClassif $ Compose Nothing
          TokenRelate -> Unit2

      NatType -> handleConstant

      EqType tyAmbient tL tR -> do
        rtyAmbient <- h id gamma (AnalyzerInput tyAmbient U1 (Just U1) maybeDDeg) (AddressInfo ["ambient type"] False omit)
        rtL <- h id gamma (AnalyzerInput tL U1 (Just tyAmbient) maybeDDeg) (AddressInfo ["left equand"] False omit)
        rtR <- h id gamma (AnalyzerInput tR U1 (Just tyAmbient) maybeDDeg) (AddressInfo ["right equand"] False omit)
        return $ case token of
          TokenSubterms -> Box1 $ EqType (unbox1 rtyAmbient) (unbox1 rtL) (unbox1 rtR)
          TokenTypes -> BoxClassif $ Compose Nothing
          TokenRelate -> Unit2

      SysType systy -> do
        rsysty <- h id gamma (AnalyzerInput systy U1 maybeMaybeD maybeDDeg)
          (AddressInfo ["system-specific type"] False EntirelyBoring)
        return $ case token of
          TokenSubterms -> Box1 $ SysType $ unbox1 rsysty
          TokenTypes -> BoxClassif $ unboxClassif $ rsysty
          TokenRelate -> Unit2

    where handleBinder ::
            (Binding Type Type sys v -> UniHSConstructor sys v) -> Binding Type Type sys v ->
            _ (AnalyzerResult option (UniHSConstructor sys) v)
          handleBinder binder binding = do
            --let bindingClassif = case maybeMaybeD of
            --      Nothing -> Nothing
            --      Just (Compose Nothing) -> Nothing
            --      Just (Compose (Just d)) -> Just $ U1 :*: Comp1 (hs2type $ UniHS $ VarWkn <$> d)
            rbinding <- h id gamma
              (AnalyzerInput binding U1 Nothing maybeDDeg)
              (AddressInfo ["binding"] False EntirelyBoring)
            return $ case token of
              TokenSubterms -> Box1 $ binder $ unbox1 rbinding
              TokenTypes -> BoxClassif $ Compose Nothing
              TokenRelate -> Unit2
              
          handleConstant = pure $ case token of
            TokenSubterms -> Box1 $ ty
            TokenTypes -> BoxClassif $ Compose Nothing
            TokenRelate -> Unit2

-------------------------

instance SysAnalyzer sys => Analyzable sys (ConstructorTerm sys) where
  type Classif (ConstructorTerm sys) = Type sys
  type Relation (ConstructorTerm sys) = ModedDegree sys
  type AnalyzerExtraInput (ConstructorTerm sys) = U1
  analyze token fromType h gamma (AnalyzerInput t U1 _ maybeRel) = Just $  do
    
    let dgamma' = ctx'mode gamma
    let dgamma = unVarFromCtx <$> dgamma'

    case t of

      ConsUniHS ty -> do
        rty <- h id gamma (AnalyzerInput ty U1 Nothing maybeRel)
          (AddressInfo ["UniHS-constructor"] False EntirelyBoring)
        return $ case token of
          TokenSubterms -> Box1 $ ConsUniHS $ unbox1 rty
          TokenTypes -> BoxClassif $ hs2type $ UniHS $ fromMaybe dgamma $ getCompose $ unboxClassif rty
          TokenRelate -> Unit2

      Lam binding -> do
        rbinding <- h id gamma (AnalyzerInput binding U1 Nothing maybeRel)
          (AddressInfo ["binding"] False EntirelyBoring)
        return $ case token of
          TokenSubterms -> Box1 $ Lam $ unbox1 rbinding
          TokenTypes ->
            let (U1 :*: Comp1 ty) = unboxClassif rbinding
            in  BoxClassif $ hs2type $ Pi $ Binding (binding'segment binding) ty
          TokenRelate -> Unit2

      Pair sigmaBinding tFst tSnd -> do
        let sigmaBindingClassif = U1 :*: Comp1 U1 --(Comp1 $ hs2type $ UniHS $ VarWkn <$> dgamma)
        rsigmaBinding <- h id gamma (AnalyzerInput sigmaBinding U1 (Just sigmaBindingClassif) maybeRel)
          (AddressInfo ["Sigma-type annotation"] False omit)
        let tyFst = _segment'content $ binding'segment $ sigmaBinding
        let tySnd = substLast2 tFst $ binding'body sigmaBinding
        rtFst <- h id gamma (AnalyzerInput tFst U1 (Just tyFst) maybeRel)
          (AddressInfo ["first component"] False omit)
        rtSnd <- h id gamma (AnalyzerInput tSnd U1 (Just tySnd) maybeRel)
          (AddressInfo ["second component"] False omit)
        return $ case token of
          TokenSubterms -> Box1 $ Pair (unbox1 rsigmaBinding) (unbox1 rtFst) (unbox1 rtSnd)
          TokenTypes -> BoxClassif $ hs2type $ Sigma sigmaBinding
          TokenRelate -> Unit2

      ConsUnit -> pure $ case token of
        TokenSubterms -> Box1 $ ConsUnit
        TokenTypes -> BoxClassif $ hs2type $ UnitType
        TokenRelate -> Unit2

      ConsBox boxSeg tUnbox -> do
        rboxSeg <- h id gamma (AnalyzerInput boxSeg U1 (Just U1) maybeRel)
          (AddressInfo ["Box-type annotation"] False omit)
        let tyUnbox = _segment'content boxSeg
        rtUnbox <- h id gamma (AnalyzerInput tUnbox U1 (Just tyUnbox) maybeRel)
          (AddressInfo ["box content"] False omit)
        return $ case token of
          TokenSubterms -> Box1 $ ConsBox (unbox1 rboxSeg) (unbox1 rtUnbox)
          TokenTypes -> BoxClassif $ hs2type $ BoxType boxSeg
          TokenRelate -> Unit2

      ConsZero -> pure $ case token of
        TokenSubterms -> Box1 $ ConsZero
        TokenTypes -> BoxClassif $ hs2type $ NatType
        TokenRelate -> Unit2

      ConsSuc t -> do
        rt <- h id gamma (AnalyzerInput t U1 (Just $ hs2type NatType) maybeRel)
          (AddressInfo ["predecessor"] False omit)
        return $ case token of
          TokenSubterms -> Box1 $ ConsSuc $ (unbox1 rt)
          TokenTypes -> BoxClassif $ hs2type $ NatType
          TokenRelate -> Unit2

      ConsRefl t -> do
        rt <- h id gamma (AnalyzerInput t U1 Nothing maybeRel)
          (AddressInfo ["self-equand"] False omit)
        return $ case token of
          TokenSubterms -> Box1 $ ConsRefl $ (unbox1 rt)
          TokenTypes -> BoxClassif $ hs2type $ EqType (unboxClassif rt) t t
          TokenRelate -> Unit2

-------------------------

instance SysAnalyzer sys => Analyzable sys (Type sys) where
  type Classif (Type sys) = U1
  type Relation (Type sys) = ModedDegree sys
  type AnalyzerExtraInput (Type sys) = U1
  analyze token fromType h gamma (AnalyzerInput (Type t) U1 _ maybeRel) = Just $ do
    let dgamma' = ctx'mode gamma
    let dgamma = unVarFromCtx <$> dgamma'
    rt <- h id gamma (AnalyzerInput t U1 (Just $ hs2type $ UniHS dgamma) maybeRel)
      (AddressInfo ["code"] True WorthMentioning)
    return $ case token of
      TokenSubterms -> Box1 $ Type $ unbox1 rt
      TokenTypes -> BoxClassif U1
      TokenRelate -> Unit2

-------------------------

instance SysAnalyzer sys => Analyzable sys (DependentEliminator sys) where
  type Classif (DependentEliminator sys) = U1
  type Relation (DependentEliminator sys) = ModedDegree sys
  type AnalyzerExtraInput (DependentEliminator sys) =
    ModedModality sys :*: Term sys :*: UniHSConstructor sys :*: (Type sys :.: VarExt)
  analyze token fromType h gamma
    (AnalyzerInput clauses (dmuElim :*: eliminee :*: tyEliminee :*: Comp1 (motive :: Type sys (VarExt v))) _ maybeRel)
    = Just $ do

    let dgamma' = ctx'mode gamma
    let dgamma = unVarFromCtx <$> dgamma'

    case (tyEliminee, clauses) of

      (Sigma binding, ElimSigma (NamedBinding nameFst (NamedBinding nameSnd pairClause))) -> do
        let segFst = Declaration
                 (DeclNameSegment nameFst)
                 (compModedModality dmuElim (_segment'modty $ binding'segment $ binding))
                 Explicit
                 (_segment'content $ binding'segment $ binding)
        let segSnd = Declaration
                 (DeclNameSegment nameSnd)
                 (VarWkn <$> dmuElim)
                 Explicit
                 (binding'body binding)
        let subst VarLast = Expr2 $ TermCons $ Pair (VarWkn . VarWkn <$> binding) (Var2 $ VarWkn VarLast) (Var2 VarLast)
            subst (VarWkn v) = Var2 $ VarWkn $ VarWkn v
        rpairClause <- h (VarWkn . VarWkn)
                         (gamma :.. VarFromCtx <$> (decl'content %~ fromType) segFst
                                :.. VarFromCtx <$> (decl'content %~ fromType) segSnd)
                         (AnalyzerInput pairClause U1
                           (Just $ swallow $ subst <$> motive)
                           (fmap (VarWkn . VarWkn) <$> maybeRel)
                         )
                         (AddressInfo ["pair clause"] False omit)
        return $ case token of
          TokenSubterms -> Box1 $ ElimSigma $ NamedBinding nameFst $ NamedBinding nameSnd $ unbox1 rpairClause
          TokenTypes -> BoxClassif U1
          TokenRelate -> Unit2
      (_, ElimSigma _) -> unreachable

      (BoxType seg, ElimBox (NamedBinding nameUnbox boxClause)) -> do
        let segUnbox = Declaration
                 (DeclNameSegment nameUnbox)
                 (compModedModality dmuElim (_segment'modty $ seg))
                 Explicit
                 (_segment'content seg)
        let subst VarLast = Expr2 $ TermCons $ ConsBox (VarWkn <$> seg) (Var2 VarLast)
            subst (VarWkn v) = Var2 $ VarWkn v
        rboxClause <- h VarWkn
                         (gamma :.. VarFromCtx <$> (decl'content %~ fromType) segUnbox)
                         (AnalyzerInput boxClause U1
                           (Just $ swallow $ subst <$> motive)
                           (fmap VarWkn <$> maybeRel)
                         )
                         (AddressInfo ["box clause"] False omit)
        return $ case token of
          TokenSubterms -> Box1 $ ElimBox $ NamedBinding nameUnbox $ unbox1 rboxClause
          TokenTypes -> BoxClassif U1
          TokenRelate -> Unit2
      (_, ElimBox _) -> unreachable

      (EmptyType, ElimEmpty) -> pure $ case token of
        TokenSubterms -> Box1 ElimEmpty
        TokenTypes -> BoxClassif U1
        TokenRelate -> Unit2
      (_, ElimEmpty) -> unreachable

      (NatType, ElimNat (zeroClause :: Term sys v) (NamedBinding namePred (NamedBinding nameHyp sucClause))) -> do
        
        rzeroClause <- h id gamma
          (AnalyzerInput zeroClause U1 (Just $ substLast2 (Expr2 $ TermCons $ ConsZero :: Term sys v) $ motive) maybeRel)
          (AddressInfo ["zero clause"] False omit)

        let segPred = Declaration
                  (DeclNameSegment $ namePred)
                  dmuElim
                  Explicit
                  (hs2type $ NatType)
        let segHyp = Declaration
                  (DeclNameSegment $ nameHyp)
                  (idModedModality $ VarWkn <$> dgamma)
                  Explicit
                  motive
        let substS :: VarExt v -> Term sys (VarExt (VarExt v))
            substS VarLast = Expr2 $ TermCons $ ConsSuc $ Var2 $ VarWkn VarLast
            substS (VarWkn v) = Var2 $ VarWkn $ VarWkn v
        rsucClause <- h (VarWkn . VarWkn)
          (gamma :.. VarFromCtx <$> (decl'content %~ fromType) segPred
                 :.. VarFromCtx <$> (decl'content %~ fromType) segHyp)
          (AnalyzerInput sucClause U1 (Just $ swallow $ substS <$> motive) (fmap (VarWkn . VarWkn) <$> maybeRel))
          (AddressInfo ["successor clause"] False omit)
            
        return $ case token of
          TokenSubterms ->
            Box1 $ ElimNat (unbox1 rzeroClause) $ NamedBinding namePred $ NamedBinding nameHyp $ unbox1 rsucClause
          TokenTypes -> BoxClassif U1
          TokenRelate -> Unit2
      (_, ElimNat _ _) -> unreachable

-------------------------

instance SysAnalyzer sys => Analyzable sys (Eliminator sys) where
  type Classif (Eliminator sys) = Type sys
  type Relation (Eliminator sys) = ModedDegree sys
  type AnalyzerExtraInput (Eliminator sys) = ModedModality sys :*: Term sys :*: UniHSConstructor sys
  analyze token fromType h gamma (AnalyzerInput eliminator (dmuElim :*: eliminee :*: tyEliminee) _ maybeRel) = Just $ do
    let dgamma' = ctx'mode gamma
    let dgamma = unVarFromCtx <$> dgamma'

    case (tyEliminee, eliminator) of

      (Pi binding, App arg) -> do
        rarg <- h id gamma (AnalyzerInput arg U1 (Just $ _segment'content $ binding'segment binding) maybeRel)
          (AddressInfo ["argument"] False omit)
        return $ case token of
          TokenSubterms -> Box1 $ App $ unbox1 rarg
          TokenTypes -> BoxClassif $ substLast2 arg $ binding'body binding
          TokenRelate -> Unit2
      (_, App arg) -> unreachable

      (Sigma binding, Fst) -> pure $ case token of
          TokenSubterms -> Box1 $ Fst
          TokenTypes -> BoxClassif $ _segment'content $ binding'segment binding
          TokenRelate -> Unit2
      (_, Fst) -> unreachable

      (Sigma binding, Snd) -> pure $ case token of
        TokenSubterms -> Box1 $ Snd
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
        TokenSubterms -> Box1 $ Unbox
        TokenTypes -> BoxClassif $ _segment'content seg
        TokenRelate -> Unit2
      (_, Unbox) -> unreachable

      (Pi binding, Funext) -> pure $ case token of
        TokenSubterms -> Box1 $ Funext
        TokenTypes -> case binding'body binding of
          TypeHS (EqType tyAmbient tL tR) -> BoxClassif $ hs2type $ EqType
            (hs2type $ Pi $           Binding (binding'segment binding) tyAmbient)
            (Expr2 $ TermCons $ Lam $ Binding (binding'segment binding) tL)
            (Expr2 $ TermCons $ Lam $ Binding (binding'segment binding) tR)
          _ -> unreachable
        TokenRelate -> Unit2
      (_, Funext) -> unreachable

      (_, ElimDep namedMotive@(NamedBinding name motive) clauses) -> do
        let seg = Declaration (DeclNameSegment name) dmuElim Explicit (hs2type tyEliminee)
        rmotive <- h VarWkn
                     (gamma :.. VarFromCtx <$> (decl'content %~ fromType) seg)
                     (AnalyzerInput motive U1 (Just U1) (fmap VarWkn <$> maybeRel))
                     (AddressInfo ["motive"] False omit)
        rclauses <- h id gamma
                      (AnalyzerInput clauses (dmuElim :*: eliminee :*: tyEliminee :*: Comp1 motive) (Just $ U1) maybeRel)
                      (AddressInfo ["clauses"] False EntirelyBoring)
        return $ case token of
          TokenSubterms -> Box1 $ ElimDep (NamedBinding name $ unbox1 rmotive) (unbox1 rclauses)
          TokenTypes -> BoxClassif $ substLast2 eliminee motive
          TokenRelate -> Unit2

      (EqType tyAmbient tL tR, ElimEq (NamedBinding nameR (NamedBinding nameEq motive)) clauseRefl) -> do
         let segR = Declaration (DeclNameSegment nameR) dmuElim Explicit tyAmbient
         let segEq = Declaration
               (DeclNameSegment nameEq)
               (VarWkn <$> dmuElim)
               Explicit
               (hs2type $ EqType (VarWkn <$> tyAmbient) (VarWkn <$> tL) (Var2 VarLast))
         rmotive <- h (VarWkn . VarWkn)
                      (gamma :.. VarFromCtx <$> (decl'content %~ fromType) segR
                             :.. VarFromCtx <$> (decl'content %~ fromType) segEq)
                      (AnalyzerInput motive U1 (Just U1) (fmap (VarWkn . VarWkn) <$> maybeRel))
                      (AddressInfo ["motive"] False omit)
         let tyReflClause = substLast2 tL $ substLast2 (Expr2 $ TermCons $ ConsRefl $ VarWkn <$> tL) $ motive
         rclauseRefl <- h id gamma (AnalyzerInput clauseRefl U1 (Just tyReflClause) maybeRel)
                          (AddressInfo ["refl clause"] False omit)
         return $ case token of
           TokenSubterms -> Box1 $ ElimEq (NamedBinding nameR (NamedBinding nameEq $ unbox1 rmotive)) (unbox1 rclauseRefl)
           TokenTypes -> BoxClassif $ substLast2 tR $ substLast2 (VarWkn <$> eliminee) $ motive
           TokenRelate -> Unit2
      (_, ElimEq _ _) -> unreachable

-------------------------

instance SysAnalyzer sys => Analyzable sys (TermNV sys) where
  type Classif (TermNV sys) = Type sys
  type Relation (TermNV sys) = ModedDegree sys
  type AnalyzerExtraInput (TermNV sys) = U1
  analyze token fromType h gamma (AnalyzerInput t U1 maybeTy maybeRel) = case t of

    TermCons c -> Just $ do
      rc <- h id gamma (AnalyzerInput c U1 maybeTy maybeRel)
        (AddressInfo ["underlying constructor"] False EntirelyBoring)
      return $ case token of
        TokenSubterms -> Box1 $ TermCons $ unbox1 rc
        TokenTypes -> BoxClassif $ unboxClassif rc
        TokenRelate -> Unit2

    TermElim dmuElim eliminee tyEliminee eliminator -> Just $ do
      let dgamma' = ctx'mode gamma
      let dgamma = unVarFromCtx <$> dgamma'
      
      rdmuElim <- h id (crispModedModality dgamma' :\\ gamma)
        (AnalyzerInput dmuElim U1 (Just $ modality'dom dmuElim :*: dgamma) (toIfRelate token (Const ModEq)))
        (AddressInfo ["modality of elimination"] False omit)
      reliminee <- h id (VarFromCtx <$> dmuElim :\\ gamma)
        (AnalyzerInput eliminee U1 (Just $ hs2type tyEliminee) (modedDivDeg dmuElim <$> maybeRel))
        (AddressInfo ["eliminee"] True omit)
      rtyEliminee <- h id (VarFromCtx <$> dmuElim :\\ gamma)
        (AnalyzerInput tyEliminee U1 (Just $ Compose $ Just dgamma) (modedDivDeg dmuElim <$> maybeRel))
        (AddressInfo ["type of eliminee"] False omit)
      reliminator <- h id gamma
        (AnalyzerInput eliminator (dmuElim :*: eliminee :*: tyEliminee) Nothing maybeRel)
        (AddressInfo ["eliminator"] False EntirelyBoring)
        
      return $ case token of
        TokenSubterms -> Box1 $ TermElim (unbox1 rdmuElim) (unbox1 reliminee) (unbox1 rtyEliminee) (unbox1 reliminator)
        TokenTypes -> BoxClassif $ unboxClassif $ reliminator
        TokenRelate -> Unit2

    TermMeta _ _ _ _ -> Nothing

    TermWildcard -> Nothing

    TermQName _ _ -> Nothing

    TermAlreadyChecked t ty -> Nothing
      {-Just $ do
      rt <- h id gamma (AnalyzerInput t U1 (Just ty) maybeRel)
      rty <- h id gamma (AnalyzerInput ty U1 (Just U1) maybeRel)
      return $ case token of
        TokenSubterms -> Box1 $ -}

    TermAlgorithm _ _ -> Nothing

    TermSys syst -> Just $ do
      rsyst <- h id gamma (AnalyzerInput syst U1 maybeTy maybeRel) (AddressInfo ["system-specific term"] True EntirelyBoring)
      return $ case token of
        TokenSubterms -> Box1 $ TermSys $ unbox1 rsyst
        TokenTypes -> BoxClassif $ unboxClassif rsyst
        TokenRelate -> Unit2

    TermProblem t -> Nothing

-------------------------

instance SysAnalyzer sys => Analyzable sys (Term sys) where
  type Classif (Term sys) = Type sys
  type Relation (Term sys) = ModedDegree sys
  type AnalyzerExtraInput (Term sys) = U1
  analyze token fromType h gamma (AnalyzerInput t U1 maybeTy maybeRel) = case t of
    Expr2 tnv -> Just $ do
      --analyze token formType h gamma (AnalyzerInput tnv U1 maybeTy maybeRel)
      rtnv <- h id gamma (AnalyzerInput tnv U1 maybeTy maybeRel) (AddressInfo ["non-variable"] True EntirelyBoring)
      return $ case token of
        TokenSubterms -> Box1 $ Expr2 $ unbox1 rtnv
        TokenTypes -> BoxClassif $ unboxClassif $ rtnv
        TokenRelate -> Unit2
    Var2 v -> Nothing

-------------------------

instance SysAnalyzer sys => Analyzable sys (Segment Type sys) where
  type Classif (Segment Type sys) = Classif (Type sys)
  type Relation (Segment Type sys) = ModedDegree sys
  type AnalyzerExtraInput (Segment Type sys) = U1
  analyze token fromType h gamma (AnalyzerInput seg@(Declaration name dmu plic ty) U1 maybeU1 maybeRel) = Just $ do
    let dgamma' = ctx'mode gamma
    let dgamma = unVarFromCtx <$> dgamma'
    
    rdmu <- h id (crispModedModality dgamma' :\\ gamma)
      (AnalyzerInput dmu U1 (Just $ modality'dom dmu :*: dgamma) (toIfRelate token $ Const ModEq))
      (AddressInfo ["modality"] True omit)
    -- TODO plic
    rty <- h id (VarFromCtx <$> dmu :\\ gamma)
      (AnalyzerInput ty U1 (Just U1) maybeRel)
      (AddressInfo ["type"] True omit)

    return $ case token of
      TokenSubterms -> Box1 $ Declaration name (unbox1 rdmu) plic (unbox1 rty)
      TokenTypes -> BoxClassif $ U1
      TokenRelate -> Unit2

-------------------------
