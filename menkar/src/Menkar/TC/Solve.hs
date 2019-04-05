{-# LANGUAGE IncoherentInstances #-}

module Menkar.TC.Solve where

import Menkar.System
import Menkar.Fine.Syntax
import Menkar.Basic.Context
import Menkar.Fine.Context
import Menkar.Fine.Judgement
import Menkar.Fine.LookupQName
import qualified Menkar.Raw.Syntax as Raw
import Menkar.Monad.Monad
import Control.Exception.AssertFalse
import Menkar.WHN

import Data.Void
import Control.Lens
import Data.Functor.Compose
import Control.Monad
import Control.Monad.Writer.Lazy
import Data.List
import Data.List.Unique
import Data.Proxy
import Data.Maybe
import Control.Monad.Trans.Maybe

{-
forceSolveMeta :: (MonadTC sys tc, Eq v, DeBruijnLevel v, Traversable t) =>
  Constraint sys ->
  Degree sys v ->
  Ctx Type sys vOrig Void ->
  Ctx (Twice2 Type) sys v Void ->
  (vOrig -> v) ->
  (v -> Maybe vOrig) ->
  Int ->
  Type sys v ->
  t v ->
  tc (Maybe (t vOrig))
forceSovleMeta parent deg gammaOrig gamma subst partialInv meta tyMeta t = do
  let maybeTOrig = sequenceA $ partialInv <$> t
  case maybeTOrig of
    
-}

isBlockedOrMeta :: Term sys v -> [Int] -> Bool
isBlockedOrMeta (Expr2 (TermMeta _ _ _ _)) _ = True
isBlockedOrMeta _ (_:_) = True
isBlockedOrMeta _ [] = False

--------------------------

newRelatedMetaModedModality :: forall sys tc v vOrig .
  (SysTC sys, MonadTC sys tc, Eq v, DeBruijnLevel v, DeBruijnLevel vOrig) =>
  Constraint sys ->
  Ctx Type sys vOrig Void ->
  Ctx (Twice2 Type) sys v Void ->
  (vOrig -> v) ->
  (v -> Maybe vOrig) ->
  ModedModality sys v ->
  Mode sys v ->
  String ->
  tc (ModedModality sys vOrig)
newRelatedMetaModedModality parent gammaOrig gamma subst partialInv dmu2 dcod reason = do
  dmu1orig <- newMetaModedModality (Just parent) gammaOrig reason
  let dmu1 = subst <$> dmu1orig
  addNewConstraint
    (JudModedModalityRel ModEq gamma (subst <$> dmu1orig) dmu2 dcod)
    (Just parent)
    reason
  return dmu1orig

--------------------------

newRelatedMetaTerm :: forall sys tc v vOrig .
  (SysTC sys, MonadTC sys tc, Eq v, DeBruijnLevel v, DeBruijnLevel vOrig) =>
  Constraint sys ->
  Eta ->
  ModedDegree sys v ->
  Ctx Type sys vOrig Void ->
  Ctx (Twice2 Type) sys v Void ->
  (vOrig -> v) ->
  (v -> Maybe vOrig) ->
  Term sys v ->
  Type sys v ->
  Type sys v ->
  MetaNeutrality ->
  String ->
  tc (Term sys vOrig)
newRelatedMetaTerm parent eta deg gammaOrig gamma subst partialInv t2 ty1 ty2 neutrality reason = do
      t1orig <- newMetaTermNoCheck (Just parent) gammaOrig neutrality Nothing reason
      let t1 = subst <$> t1orig
      addNewConstraint
        (JudTermRel eta (_degree'deg deg) gamma (Twice2 t1 t2) (Twice2 ty1 ty2))
        (Just parent)
        reason
      return t1orig

newRelatedMetaType :: forall sys tc v vOrig .
  (SysTC sys, MonadTC sys tc, Eq v, DeBruijnLevel v, DeBruijnLevel vOrig) =>
  Constraint sys ->
  ModedDegree sys v ->
  Ctx Type sys vOrig Void ->
  Ctx (Twice2 Type) sys v Void ->
  (vOrig -> v) ->
  (v -> Maybe vOrig) ->
  Type sys v ->
  String ->
  tc (Type sys vOrig)
newRelatedMetaType parent deg gammaOrig gamma subst partialInv ty2 reason = do
      ty1orig <- Type <$> newMetaTermNoCheck (Just parent) gammaOrig MetaBlocked Nothing reason
      let ty1 = subst <$> ty1orig
      addNewConstraint
        (JudTypeRel (_degree'deg deg) gamma (Twice2 ty1 ty2))
        (Just parent)
        reason
      return ty1orig

--------------------------

newRelatedSegment :: (SysTC sys, MonadTC sys tc, Eq v, DeBruijnLevel v, DeBruijnLevel vOrig) =>
  Constraint sys ->
  ModedDegree sys v ->
  Ctx Type sys vOrig Void ->
  Ctx (Twice2 Type) sys v Void ->
  (vOrig -> v) ->
  (v -> Maybe vOrig) ->
  Segment Type sys v ->
  tc (Segment Type sys vOrig)
newRelatedSegment parent deg gammaOrig gamma subst partialInv segment2 = do
  let dgammaOrig' = ctx'mode gammaOrig
  let dgamma'     = ctx'mode gamma
  --let dgamma = unVarFromCtx <$> dgamma'
  let dmu2 = _decl'modty segment2
  dmu1orig <- newRelatedMetaModedModality
                parent
                (crispModedModality dgammaOrig' :\\ gammaOrig)
                (crispModedModality dgamma'     :\\ gamma)
                subst partialInv dmu2
                (unVarFromCtx <$> ctx'mode gamma)
                "Inferring segment modality."
  let dmu1 = subst <$> dmu1orig
  let ty2 = _decl'content segment2
  ty1orig <- newRelatedMetaType
               parent
               (modedDivDeg dmu1 deg)
               (VarFromCtx <$> dmu1orig :\\ gammaOrig)
               (VarFromCtx <$> dmu2 :\\ gamma)
               subst
               partialInv
               ty2
               "Inferring segment type."
  -- CMODE: plicity
  return $ Declaration
    (_decl'name segment2)
    dmu1orig
    (fromMaybe Explicit $ sequenceA $ partialInv <$> _decl'plicity segment2)
    ty1orig

newRelatedBinding :: (SysTC sys, MonadTC sys tc, Eq v, DeBruijnLevel v, DeBruijnLevel vOrig) =>
  Constraint sys ->
  ModedDegree sys v ->
  Ctx Type sys vOrig Void ->
  Ctx (Twice2 Type) sys v Void ->
  (vOrig -> v) ->
  (v -> Maybe vOrig) ->
  Binding Type Term sys v ->
  Type sys (VarExt v) ->
  Type sys (VarExt v) ->
  tc (Binding Type Term sys vOrig)
newRelatedBinding parent deg gammaOrig gamma subst partialInv binding2 tyBody1 tyBody2 = do
  let segment2 = binding'segment binding2
  segment1orig <- newRelatedSegment parent deg gammaOrig gamma subst partialInv segment2
  let segment1 = subst <$> segment1orig
  let dom1 = _segment'content $ segment1
  let fmapPartialInv :: VarExt _ -> Maybe (VarExt _)
      fmapPartialInv VarLast = Just VarLast
      fmapPartialInv (VarWkn v) = VarWkn <$> partialInv v
  body1orig <- newRelatedMetaTerm
                 parent
                 (Eta True)
                 (VarWkn <$> deg)
                 (gammaOrig :.. VarFromCtx <$> segment1orig)
                 (gamma :.. VarFromCtx <$> over decl'content (\dom2 -> Twice2 dom1 dom2) segment2)
                 (fmap subst)
                 fmapPartialInv
                 (binding'body binding2)
                 tyBody1
                 tyBody2
                 MetaBlocked
                 "Inferring body."
  return $ Binding segment1orig body1orig

------------------------------------

newRelatedUniHSConstructor :: (SysTC sys, MonadTC sys tc, Eq v, DeBruijnLevel v, DeBruijnLevel vOrig) =>
  Constraint sys ->
  ModedDegree sys v ->
  Ctx Type sys vOrig Void ->
  Ctx (Twice2 Type) sys v Void ->
  (vOrig -> v) ->
  (v -> Maybe vOrig) ->
  UniHSConstructor sys v ->
  tc (UniHSConstructor sys vOrig)
newRelatedUniHSConstructor parent deg gammaOrig gamma subst partialInv t2 = do
  let d      = unVarFromCtx <$> ctx'mode gamma
  let d1orig = unVarFromCtx <$> ctx'mode gammaOrig
  case t2 of
    UniHS d2 {-lvl2-} -> do
      --let nat = Type $ Expr2 $ TermCons $ ConsUniHS $ NatType
      --lvl1orig <- newRelatedMetaTerm parent topDeg gammaOrig gamma subst partialInv lvl2 nat nat "Inferring level."
                --newMetaTermNoCheck (Just parent) topDeg gammaOrig nat "Inferring level."
      return $ UniHS d1orig --lvl1orig
    Pi binding2 -> do
      let uni = hs2type $ UniHS d --(Expr2 $ TermWildcard)
      binding1orig <-
        newRelatedBinding parent deg gammaOrig gamma subst partialInv binding2 (VarWkn <$> uni) (VarWkn <$> uni)
      return $ Pi $ binding1orig
    Sigma binding2 -> do
      let uni = hs2type $ UniHS d --(Expr2 $ TermWildcard)
      binding1orig <-
        newRelatedBinding parent deg gammaOrig gamma subst partialInv binding2 (VarWkn <$> uni) (VarWkn <$> uni)
      return $ Sigma $ binding1orig
    EmptyType -> return EmptyType
    UnitType -> return UnitType
    BoxType boxSeg2 -> do
      boxSeg1orig <-
        newRelatedSegment parent deg gammaOrig gamma subst partialInv boxSeg2
      return $ BoxType $ boxSeg1orig
    NatType -> return NatType
    EqType tyAmbient2 tL2 tR2 -> do
      tyAmbient1orig <- newRelatedMetaType parent deg gammaOrig gamma subst partialInv tyAmbient2 "Inferring ambient type."
      let tyAmbient1 = subst <$> tyAmbient1orig
      tL1orig <-
        newRelatedMetaTerm parent (Eta True) deg gammaOrig gamma subst partialInv tL2 tyAmbient1 tyAmbient2
          MetaBlocked "Inferring left equand."
      tR1orig <-
        newRelatedMetaTerm parent (Eta True) deg gammaOrig gamma subst partialInv tR2 tyAmbient1 tyAmbient2
          MetaBlocked "Inferring right equand."
      return $ EqType tyAmbient1orig tL1orig tR1orig

newRelatedConstructorTerm :: forall sys tc v vOrig .
  (SysTC sys, MonadTC sys tc, Eq v, DeBruijnLevel v, DeBruijnLevel vOrig) =>
  Constraint sys ->
  ModedDegree sys v ->
  Ctx Type sys vOrig Void ->
  Ctx (Twice2 Type) sys v Void ->
  (vOrig -> v) ->
  (v -> Maybe vOrig) ->
  ConstructorTerm sys v ->
  Type sys v ->
  Type sys v ->
  [Int] ->
  [Int] ->
  (String -> tc ()) ->
  tc (Maybe (ConstructorTerm sys vOrig))
newRelatedConstructorTerm parent deg gammaOrig gamma subst partialInv t2 ty1 ty2 metasTy1 metasTy2 alternative =
  case t2 of
    ConsUniHS c2 -> do
      c1orig <- newRelatedUniHSConstructor parent deg gammaOrig gamma subst partialInv c2
      return $ Just $ ConsUniHS $ c1orig
    Lam binding2 -> do
      case (isBlockedOrMeta (unType ty1) metasTy1, ty1,
            isBlockedOrMeta (unType ty2) metasTy2, ty2) of
        (False, TypeHS (Pi piBinding1),
         False, TypeHS (Pi piBinding2)) -> do
            let cod1 = Type $ binding'body piBinding1
            let cod2 = Type $ binding'body piBinding2
            binding1orig <- newRelatedBinding parent deg gammaOrig gamma subst partialInv binding2 cod1 cod2
            return $ Just $ Lam binding1orig
        (False, _, False, _) -> tcFail parent "Terms are presumed to be well-typed."
        (_    , _, _    , _) -> Nothing <$ alternative "Need to know codomains of pi-types."
    Pair sigmaBindingPair2 tmFst2 tmSnd2 -> do
      case (isBlockedOrMeta (unType ty1) metasTy1, ty1,
            isBlockedOrMeta (unType ty2) metasTy2, ty2) of
        (False, TypeHS (Sigma sigmaBinding1),
         False, TypeHS (Sigma sigmaBinding2)) -> do
            let uni :: Type sys v
                uni = hs2type $ UniHS $ unVarFromCtx <$> ctx'mode gamma
            ---------
            sigmaBindingPair1orig <- newRelatedBinding
                                       parent deg
                                       gammaOrig gamma
                                       subst partialInv
                                       sigmaBindingPair2
                                       (VarWkn <$> uni) (VarWkn <$> uni)
            let sigmaBindingPair1 = subst <$> sigmaBindingPair1orig
            ---------
            let dmuPair1orig = _segment'modty $ binding'segment sigmaBindingPair1orig
            let dmuPair1     = _segment'modty $ binding'segment sigmaBindingPair1
            let dmuPair2     = _segment'modty $ binding'segment sigmaBindingPair2
            ---------
            let tyFst1 = _segment'content $ binding'segment sigmaBinding1
            let tyFst2 = _segment'content $ binding'segment sigmaBinding2
            ---------
            tmFst1orig <- newRelatedMetaTerm parent (Eta True)
                            (modedDivDeg dmuPair2 deg)
                            (VarFromCtx <$> dmuPair1orig :\\ gammaOrig)
                            (VarFromCtx <$> dmuPair2 :\\ gamma)
                            subst partialInv tmFst2 tyFst1 tyFst2
                            MetaBlocked "Inferring first component."
            let tmFst1 = subst <$> tmFst1orig
            ---------
            let tySnd1 = substLast2 tmFst1 $ Type $ binding'body sigmaBinding1
            let tySnd2 = substLast2 tmFst2 $ Type $ binding'body sigmaBinding2
            ---------
            tmSnd1orig <- newRelatedMetaTerm parent (Eta True) deg gammaOrig gamma subst partialInv tmSnd2 tySnd1 tySnd2
                            MetaBlocked "Inferring second component."
            let tmSnd1 = subst <$> tmSnd1orig
            ---------
            return $ Just $ Pair sigmaBindingPair1orig tmFst1orig tmSnd1orig
        (False, _, False, _) -> tcFail parent "Terms are presumed to be well-typed."
        (_    , _, _    , _) -> Nothing <$ alternative "Need to know component types of sigma-types."
    ConsUnit -> return $ Just ConsUnit
    ConsBox boxSegTerm2 tmUnbox2 -> do
      case (isBlockedOrMeta (unType ty1) metasTy1, ty1,
            isBlockedOrMeta (unType ty2) metasTy2, ty2) of
        (False, TypeHS (BoxType boxSeg1),
         False, TypeHS (BoxType boxSeg2)) -> do
            boxSegTerm1orig <- newRelatedSegment
                                       parent deg
                                       gammaOrig gamma
                                       subst partialInv
                                       boxSegTerm2
            let boxSegTerm1 = subst <$> boxSegTerm1orig
            ---------
            let dmuTerm1orig = _segment'modty boxSegTerm1orig
            let dmuTerm1     = _segment'modty boxSegTerm1
            let dmuTerm2     = _segment'modty boxSegTerm2
            ---------
            let tyUnbox1 = _segment'content boxSeg1
            let tyUnbox2 = _segment'content boxSeg2
            ---------
            tmUnbox1orig <- newRelatedMetaTerm parent (Eta True)
                            (modedDivDeg dmuTerm2 deg)
                            (VarFromCtx <$> dmuTerm1orig :\\ gammaOrig)
                            (VarFromCtx <$> dmuTerm2 :\\ gamma)
                            subst partialInv tmUnbox2 tyUnbox1 tyUnbox2
                            MetaBlocked "Inferring box content."
            let tmUnbox1 = subst <$> tmUnbox1orig
            ---------
            return $ Just $ ConsBox boxSegTerm1orig tmUnbox1orig
        (False, _, False, _) -> tcFail parent "Terms are presumed to be well-typed."
        (_    , _, _    , _) -> Nothing <$ alternative "Need to know content types of box types."
    ConsZero -> return $ Just ConsZero
    ConsSuc t2 -> do
      let nat = hs2type $ NatType
      t1orig <- newRelatedMetaTerm parent (Eta True) deg
                  gammaOrig gamma subst partialInv t2 nat nat MetaBlocked "Inferring predecessor."
      return $ Just $ ConsSuc t1orig
    ConsRefl -> return $ Just ConsRefl

------------------------------------

newRelatedDependentEliminator :: forall sys tc v vOrig .
  (SysTC sys, MonadTC sys tc, Eq v, DeBruijnLevel v, DeBruijnLevel vOrig) =>
  Constraint sys ->
  ModedDegree sys v ->
  Ctx Type sys vOrig Void ->
  Ctx (Twice2 Type) sys v Void ->
  (vOrig -> v) ->
  (v -> Maybe vOrig) ->
  ModedModality sys vOrig {-^ Modality of elimination. -} ->
  ModedModality sys v     {-^ Modality of elimination. -} ->
  Term sys vOrig ->
  Term sys v ->
  UniHSConstructor sys vOrig ->
  UniHSConstructor sys v ->
  NamedBinding Type sys vOrig ->
  NamedBinding Type sys v ->
  DependentEliminator sys v ->
  Type sys v ->
  Type sys v ->
  tc (DependentEliminator sys vOrig)
newRelatedDependentEliminator parent deg gammaOrig gamma subst partialInv
  dmu1orig dmu2
  eliminee1orig eliminee2
  tyEliminee1orig tyEliminee2
  motive1orig motive2
  clauses2
  ty1 ty2 = do
  let dmu1 = subst <$> dmu1orig
  let tyEliminee1 = subst <$> tyEliminee1orig
  let motive1 = subst <$> motive1orig
  case clauses2 of
    ElimSigma clausePair2 -> case (tyEliminee1orig, tyEliminee2) of
      (Sigma sigmaBinding1orig, Sigma sigmaBinding2) -> do
        let sigmaBinding1 = subst <$> sigmaBinding1orig
        let nameFst = _namedBinding'name clausePair2
        let nameSnd = _namedBinding'name $ _namedBinding'body clausePair2
        let segFst1orig = Declaration
                            (DeclNameSegment nameFst)
                            (compModedModality dmu1orig (_segment'modty $ binding'segment $ sigmaBinding1orig))
                            Explicit
                            (_segment'content $ binding'segment $ sigmaBinding1orig)
        let segFst      = Declaration
                            (DeclNameSegment nameFst)
                            (compModedModality dmu1     (_segment'modty $ binding'segment $ sigmaBinding1))
                            Explicit
                            (Twice2
                              (_segment'content $ binding'segment $ sigmaBinding1)
                              (_segment'content $ binding'segment $ sigmaBinding2)
                            )
        let segSnd1orig = Declaration
                            (DeclNameSegment nameSnd)
                            (VarWkn <$> dmu1orig)
                            Explicit
                            (Type $ binding'body sigmaBinding1orig)
        let segSnd      = Declaration
                            (DeclNameSegment nameSnd)
                            (VarWkn <$> dmu1)
                            Explicit
                            (Twice2
                              (Type $ binding'body sigmaBinding1)
                              (Type $ binding'body sigmaBinding2)
                            )
        let substPair' :: Binding Type Term _ _ -> VarExt _ -> Term _ (VarExt (VarExt _))
            substPair' sigmaBinding VarLast =
                Expr2 $ TermCons $ Pair (VarWkn . VarWkn <$> sigmaBinding) (Var2 $ VarWkn VarLast) (Var2 VarLast)
            substPair' sigmaBinding (VarWkn v) = Var2 $ VarWkn $ VarWkn $ v
            substPair :: Binding Type Term _ _ -> Type _ (VarExt _) -> Type _ (VarExt (VarExt _))
            substPair sigmaBinding = swallow . fmap (substPair' sigmaBinding)
        let ty1 = substPair sigmaBinding1 $ _namedBinding'body motive1
        let ty2 = substPair sigmaBinding2 $ _namedBinding'body motive2
        clausePair1orig <- clausePair2 & (namedBinding'body . namedBinding'body $ \ t2 ->
          newRelatedMetaTerm
            parent (Eta True)
            (VarWkn . VarWkn <$> deg)
            (gammaOrig :.. VarFromCtx <$> segFst1orig :.. VarFromCtx <$> segSnd1orig)
            (gamma     :.. VarFromCtx <$> segFst      :.. VarFromCtx <$> segSnd)
            (fmap $ fmap subst)
            (sequenceA . fmap sequenceA . (fmap $ fmap partialInv))
            t2 ty1 ty2
            MetaBlocked
            "Inferring pair clause."
          )
        return $ ElimSigma clausePair1orig
      (_, _) -> unreachable
    ElimBox boxClause2 -> case (tyEliminee1orig, tyEliminee2) of
      (BoxType boxSeg1orig, BoxType boxSeg2) -> do
        let boxSeg1 = subst <$> boxSeg1orig
        let nameUnbox = _namedBinding'name boxClause2
        let segUnbox1orig = Declaration
                              (DeclNameSegment nameUnbox)
                              (compModedModality dmu1orig (_segment'modty boxSeg1orig))
                              Explicit
                              (_segment'content boxSeg1orig)
        let segUnbox =     Declaration
                              (DeclNameSegment nameUnbox)
                              (compModedModality dmu1     (_segment'modty boxSeg2))
                              Explicit
                              (Twice2
                                (_segment'content boxSeg1)
                                (_segment'content boxSeg2)
                              )
        let substBox :: Segment Type sys v -> VarExt v -> Term sys (VarExt v)
            substBox boxSeg VarLast = Expr2 $ TermCons $ ConsBox (VarWkn <$> boxSeg) $ Var2 VarLast
            substBox boxSeg (VarWkn v) = Var2 $ VarWkn v
        let ty1 = swallow $ substBox boxSeg1 <$> _namedBinding'body motive1
        let ty2 = swallow $ substBox boxSeg1 <$> _namedBinding'body motive2
        boxClause1orig <- boxClause2 & (namedBinding'body $ \ t2 ->
          newRelatedMetaTerm
            parent (Eta True)
            (VarWkn <$> deg)
            (gammaOrig :.. VarFromCtx <$> segUnbox1orig)
            (gamma     :.. VarFromCtx <$> segUnbox)
            (fmap subst)
            (sequenceA . fmap partialInv)
            t2 ty1 ty2
            MetaBlocked
            "Inferring box clause."
          )
        return $ ElimBox boxClause1orig
      (_, _) -> unreachable
    ElimEmpty -> return ElimEmpty
    ElimNat clauseZero2 clauseSuc2 -> do
      let tyCZ1 = substLast2 (Expr2 $ TermCons $ ConsZero :: Term sys _) $ _namedBinding'body motive1
      let tyCZ2 = substLast2 (Expr2 $ TermCons $ ConsZero :: Term sys _) $ _namedBinding'body motive2
      clauseZero1orig <-
        newRelatedMetaTerm parent (Eta True) deg gammaOrig gamma subst partialInv clauseZero2 tyCZ1 tyCZ2
          MetaBlocked "Inferring zero clause."
      -----------------
      let nat = hs2type NatType
      let namePred = _namedBinding'name clauseSuc2
      let nameHyp  = _namedBinding'name $ _namedBinding'body clauseSuc2
      let segPred1orig = Declaration (DeclNameSegment namePred) dmu1orig Explicit nat
      let segPred      = Declaration (DeclNameSegment namePred) dmu1     Explicit (Twice2 nat nat)
      let segHyp1orig = Declaration
                          (DeclNameSegment nameHyp)
                          (idModedModality $ VarWkn . unVarFromCtx <$> ctx'mode gammaOrig)
                          Explicit
                          (_namedBinding'body motive1orig)
      let segHyp      = Declaration
                          (DeclNameSegment nameHyp)
                          (idModedModality $ VarWkn . unVarFromCtx <$> ctx'mode gamma)
                          Explicit
                          (Twice2
                            (_namedBinding'body motive1)
                            (_namedBinding'body motive2)
                          )
      let substS :: VarExt v -> Term sys (VarExt (VarExt v))
          substS VarLast = Expr2 $ TermCons $ ConsSuc $ Var2 $ VarWkn VarLast
          substS (VarWkn v) = Var2 $ VarWkn $ VarWkn v
      let tyCS1 = swallow $ substS <$> _namedBinding'body motive1
      let tyCS2 = swallow $ substS <$> _namedBinding'body motive2
      clauseSuc1orig <- flip namedBinding'body clauseSuc2 $ namedBinding'body $ \ t2 ->
        newRelatedMetaTerm
          parent (Eta True)
          (VarWkn . VarWkn <$> deg)
          (gammaOrig :.. VarFromCtx <$> segPred1orig :.. VarFromCtx <$> segHyp1orig)
          (gamma     :.. VarFromCtx <$> segPred      :.. VarFromCtx <$> segHyp)
          (fmap $ fmap subst)
          (sequenceA . fmap sequenceA . (fmap $ fmap partialInv))
          t2 tyCS1 tyCS2
          MetaBlocked
          "Inferring successor clause."
      return $ ElimNat clauseZero1orig clauseSuc1orig

newRelatedEliminator :: forall sys tc v vOrig .
  (SysTC sys, MonadTC sys tc, Eq v, DeBruijnLevel v, DeBruijnLevel vOrig) =>
  Constraint sys ->
  ModedDegree sys v ->
  Ctx Type sys vOrig Void ->
  Ctx (Twice2 Type) sys v Void ->
  (vOrig -> v) ->
  (v -> Maybe vOrig) ->
  ModedModality sys vOrig {-^ Modality of elimination. -} ->
  ModedModality sys v {-^ Modality of elimination. -} ->
  Term sys vOrig ->
  Term sys v ->
  UniHSConstructor sys vOrig ->
  UniHSConstructor sys v ->
  Eliminator sys v ->
  Type sys v ->
  Type sys v ->
  tc (Eliminator sys vOrig)
newRelatedEliminator parent deg gammaOrig gamma subst partialInv
  dmu1orig dmu2
  eliminee1orig eliminee2
  tyEliminee1orig tyEliminee2
  eliminator2
  ty1 ty2 = do
  let dmu1 = subst <$> dmu1orig
  let eliminee1 = subst <$> eliminee1orig
  let tyEliminee1 = subst <$> tyEliminee1orig
  case eliminator2 of
    App arg2 -> case (tyEliminee1orig, tyEliminee2) of
      (Pi piBinding1orig, Pi piBinding2) -> do
        let piBinding1 = subst <$> piBinding1orig
        let dmuPi1orig = _segment'modty $ binding'segment piBinding1orig
        let dmuPi2     = _segment'modty $ binding'segment piBinding2
        let dmuPi1 = subst <$> dmuPi1orig
        arg1orig <- newRelatedMetaTerm
                      parent (Eta True)
                      (modedDivDeg dmuPi1 deg)
                      (VarFromCtx <$> dmuPi1orig :\\ gammaOrig)
                      (VarFromCtx <$> dmuPi1     :\\ gamma)
                      subst
                      partialInv
                      arg2
                      (_segment'content $ binding'segment piBinding1)
                      (_segment'content $ binding'segment piBinding2)
                      MetaBlocked
                      "Inferring argument."
        return $ App arg1orig
      (_, _) -> unreachable
    Fst -> return Fst
    Snd -> return Snd
    Unbox -> return Unbox
    Funext -> return Funext
    ElimDep motive2 clauses2 -> do
      let seg1orig = Declaration (DeclNameSegment $ _namedBinding'name motive2) dmu1orig Explicit
                       (Type $ Expr2 $ TermCons $ ConsUniHS $ tyEliminee1orig)
      let seg      = Declaration (DeclNameSegment $ _namedBinding'name motive2) dmu1     Explicit $ Twice2
                       (Type $ Expr2 $ TermCons $ ConsUniHS $ tyEliminee1)
                       (Type $ Expr2 $ TermCons $ ConsUniHS $ tyEliminee2)
      motive1orig <- flip namedBinding'body motive2 $ \ ty2 ->
                       newRelatedMetaType
                         parent
                         (VarWkn <$> deg)
                         (gammaOrig :.. VarFromCtx <$> seg1orig)
                         (gamma     :.. VarFromCtx <$> seg)
                         (fmap subst)
                         (sequenceA . fmap partialInv)
                         ty2
                         "Inferring motive."
      clauses1orig <- newRelatedDependentEliminator parent deg gammaOrig gamma subst partialInv
                        dmu1orig dmu2
                        eliminee1orig eliminee2
                        tyEliminee1orig tyEliminee2
                        motive1orig motive2
                        clauses2
                        ty1 ty2
      return $ ElimDep motive1orig clauses1orig
    ElimEq motive2 crefl2 -> case (tyEliminee1orig, tyEliminee2) of
      (EqType tyAmbient1orig tL1orig tR1orig, EqType tyAmbient2 tL2 tR2) -> do
        let tyAmbient1 = subst <$> tyAmbient1orig
        let tL1 = subst <$> tL1orig
        let tR1 = subst <$> tR1orig
        let segR1orig = Declaration (DeclNameSegment $ _namedBinding'name motive2) dmu1orig Explicit
                          tyAmbient1orig
        let segR      = Declaration (DeclNameSegment $ _namedBinding'name motive2) dmu1     Explicit $ Twice2
                          tyAmbient1
                          tyAmbient2
        let segEq1orig = Declaration (DeclNameSegment $ _namedBinding'name $ _namedBinding'body motive2)
                           (VarWkn <$> dmu1orig) Explicit
                           (hs2type $ EqType (VarWkn <$> tyAmbient1orig) (VarWkn <$> tL1orig) (Var2 VarLast))
        let segEq      = Declaration (DeclNameSegment $ _namedBinding'name $ _namedBinding'body motive2)
                           (VarWkn <$> dmu1    ) Explicit $
                         Twice2
                           (hs2type $ EqType (VarWkn <$> tyAmbient1) (VarWkn <$> tL1) (Var2 VarLast))
                           (hs2type $ EqType (VarWkn <$> tyAmbient2) (VarWkn <$> tL2) (Var2 VarLast))
        motive1orig <- flip (namedBinding'body . namedBinding'body) motive2 $ \ty2 ->
                         newRelatedMetaType
                           parent
                           (VarWkn . VarWkn <$> deg)
                           (gammaOrig :.. VarFromCtx <$> segR1orig :.. VarFromCtx <$> segEq1orig)
                           (gamma     :.. VarFromCtx <$> segR      :.. VarFromCtx <$> segEq     )
                           (fmap $ fmap subst)
                           (sequenceA . fmap sequenceA . fmap (fmap partialInv))
                           ty2
                           "Inferring motive."
        let motive1 = subst <$> motive1orig
        let refl :: forall w . Term sys w
            refl = Expr2 $ TermCons $ ConsRefl
        crefl1orig <- newRelatedMetaTerm parent (Eta True) deg gammaOrig gamma subst partialInv
                        crefl2
                        (substLast2 tL1 $ substLast2 refl $ _namedBinding'body $ _namedBinding'body motive1)
                        (substLast2 tL2 $ substLast2 refl $ _namedBinding'body $ _namedBinding'body motive2)
                        MetaBlocked
                        "Inferring refl clause."
        return $ ElimEq motive1orig crefl1orig
      (_, _) -> unreachable

------------------------------------

{-
{-| A meta is pure if it has undergone a substitution that can be inverted in the following sense:
    All variables have been substituted with variables - all different - and the inverse substitution is well-typed
    for all variables for which it is defined.

    This method returns @'Nothing'@ if this is presently unclear, @'Just' 'True'@ if the meta is pure, and
    @'Just' 'False'@ if it is false.
-}
checkMetaPure :: forall sys tc v vOrig .
  (SysTC sys, MonadTC sys tc, Eq v, DeBruijnLevel v, DeBruijnLevel vOrig) =>
  Constraint sys ->
  Ctx Type sys vOrig Void ->
  Ctx Type sys v Void ->
  (vOrig -> v) ->
  Type sys v ->
  tc (Maybe Bool)
checkMetaPure parent gammaOrig gamma subst ty = do
  --let proxyOrig = ctx'sizeProxy gammaOrig
  --let proxy     = ctx'sizeProxy gamma
  --let varsOrig = listAll proxyOrig
  --let vars     = listAll proxy
  let ldivSegmentOrig u = unVarFromCtx <$> lookupVar gammaOrig u
  let ldivSegment     v = unVarFromCtx <$> lookupVar gamma     v
  let dmuOrig u = divModedModality
                    (_leftDivided'modality $ ldivSegmentOrig u)
                    (_segment'modty $ _leftDivided'content $ ldivSegmentOrig u)
  let dmu     v = divModedModality
                    (_leftDivided'modality $ ldivSegment v)
                    (_segment'modty $ _leftDivided'content $ ldivSegment v)
  -- require that forall u . dmuOrig u <= dmu (subst u)
  let condition :: vOrig -> tc (Maybe Bool)
      condition u = leqMod
        (subst <$> (modality'dom $ dmuOrig u))
        (subst . unVarFromCtx <$> ctx'mode gammaOrig)
        (subst <$> (modality'mod $ dmuOrig u))
        (modality'mod $ dmu $ subst u)
  fmap (fmap and . sequenceA) $ sequenceA $ condition <$> listAll Proxy
-}

--------------------------------------------------------
-- NO ETA --
--------------------------------------------------------

solveMetaAgainstWHNF :: forall sys tc v vOrig .
  (SysTC sys, MonadTC sys tc, Eq v, DeBruijnLevel v, DeBruijnLevel vOrig) =>
  Constraint sys ->
  ModedDegree sys v ->
  Ctx Type sys vOrig Void ->
  Ctx (Twice2 Type) sys v Void ->
  (vOrig -> v) ->
  (v -> Maybe vOrig) ->
  Term sys v ->
  Type sys v ->
  Type sys v ->
  [Int] ->
  [Int] ->
  (String -> tc ()) ->
  tc (Maybe (Term sys vOrig))
solveMetaAgainstWHNF parent deg gammaOrig gamma subst partialInv t2 ty1 ty2 metasTy1 metasTy2 alternative = do
  let dgammaOrig' = ctx'mode gammaOrig
  let dgamma'     = ctx'mode gamma
  case t2 of
    Var2 v -> case partialInv v of
      Nothing -> Nothing <$ alternative "Cannot instantiate metavariable with a variable that it does not depend on."
      Just u -> return $ Just $ Var2 u
    Expr2 t2 -> case t2 of
      TermCons c2 -> do
        maybeC1orig <- newRelatedConstructorTerm parent deg gammaOrig gamma subst partialInv c2
                    ty1 ty2 metasTy1 metasTy2 alternative
        return $ Expr2 . TermCons <$> maybeC1orig
      TermElim dmu2 eliminee2 tyEliminee2 eliminator2 -> do
        dmu1orig <- newRelatedMetaModedModality
                      parent
                      (crispModedModality dgammaOrig' :\\ gammaOrig)
                      (crispModedModality dgamma'     :\\ gamma)
                      subst
                      partialInv
                      dmu2
                      (unVarFromCtx <$> ctx'mode gamma)
                      "Inferring elimination mode and modality."
        let dmu1 = subst <$> dmu1orig
        tyEliminee1orig <- newRelatedUniHSConstructor
                             parent
                             (modedDivDeg dmu1 deg)
                             (VarFromCtx <$> dmu1orig :\\ gammaOrig)
                             (VarFromCtx <$> dmu1 :\\ gamma)
                             subst
                             partialInv
                             tyEliminee2
        let tyEliminee1 = subst <$> tyEliminee1orig
        eliminee1orig <- newRelatedMetaTerm
                             parent (Eta False)
                             (modedDivDeg dmu1 deg)
                             (VarFromCtx <$> dmu1orig :\\ gammaOrig)
                             (VarFromCtx <$> dmu1 :\\ gamma)
                             subst
                             partialInv
                             eliminee2
                             (hs2type $ tyEliminee1)
                             (hs2type $ tyEliminee2)
                             MetaNeutral
                               {- This is one reason this flag exists:
                                  eliminees should not be solved by eta-expansion!
                                  Doing so could create loops. -}
                             "Inferring eliminee."
        let eliminee1 = subst <$> eliminee1orig
        eliminator1orig <- newRelatedEliminator parent deg gammaOrig gamma subst partialInv
                             dmu1orig dmu2
                             eliminee1orig eliminee2
                             tyEliminee1orig tyEliminee2
                             eliminator2
                             ty1 ty2
        return $ Just $ Expr2 $ TermElim dmu1orig eliminee1orig tyEliminee1orig eliminator1orig
      TermMeta MetaBlocked _ _ _ -> unreachable
      TermMeta MetaNeutral _ _ _ -> unreachable
      TermWildcard -> unreachable
      TermQName _ _ -> unreachable
      TermAlreadyChecked _ _ -> unreachable
      TermAlgorithm _ _ -> unreachable
      TermProblem _ -> do
        tcFail parent "Nonsensical term."
      TermSys t2 -> newRelatedSysTerm parent deg gammaOrig gamma subst partialInv t2 ty1 ty2 alternative

{-| Precondition: @partialInv . subst = Just@.
-}
solveMetaImmediately :: (SysTC sys, MonadTC sys tc, Eq v, DeBruijnLevel v, DeBruijnLevel vOrig) =>
  Constraint sys ->
  Ctx Type sys vOrig Void ->
  Ctx (Twice2 Type) sys v Void ->
  (vOrig -> v) ->
  (v -> Maybe vOrig) ->
  Term sys v ->
  Type sys v ->
  Type sys v ->
  [Int] ->
  [Int] ->
  (String -> tc ()) ->
  tc (Maybe (Term sys vOrig))
solveMetaImmediately parent gammaOrig gamma subst partialInv t2 ty1 ty2 metasTy1 metasTy2 alternative = do
  -- Try to write t2 in gammaOrig
  let dgamma' = ctx'mode gamma
      dgamma = unVarFromCtx <$> dgamma'
  let maybeT2orig = sequenceA $ partialInv <$> t2
  case maybeT2orig of
    -- If it works, return that.
    Just t2orig -> return $ Just t2orig
    -- If t2 contains variables not in gammaOrig: solve against WHNF
    Nothing ->
      solveMetaAgainstWHNF parent
        (modedEqDeg dgamma) gammaOrig gamma subst partialInv t2 ty1 ty2 metasTy1 metasTy2 alternative

--------------------------------------------------------
-- ALWAYS ETA --
--------------------------------------------------------

{-| Returns an eta-expansion if eta is certainly allowed, @Just Nothing@ if it's not allowed, and @Nothing@ if unclear.
-}
etaExpand ::
  (SysTC sys, MonadTC sys tc, DeBruijnLevel v) =>
  Constraint sys ->
  Ctx Type sys v Void ->
  Term sys v ->
  UniHSConstructor sys v ->
  tc (Maybe (Maybe (Term sys v)))
etaExpand parent gamma t (Pi piBinding) = do
  body <- newMetaTerm
            (Just parent)
            --(eqDeg :: Degree sys _)
            (gamma :.. (VarFromCtx <$> binding'segment piBinding))
            (Type $ binding'body piBinding)
            MetaBlocked
            "Infer function body."
  return $ Just $ Just $ Expr2 $ TermCons $ Lam $ Binding (binding'segment piBinding) body
etaExpand parent gamma t (Sigma sigmaBinding) = do
  let dgamma' = ctx'mode gamma
  let dgamma = unVarFromCtx <$> dgamma'
  let dmu = _segment'modty $ binding'segment $ sigmaBinding
  allowsEta parent (crispModedModality dgamma' :\\ gamma) dmu dgamma "Need to know if eta is allowed." >>= \case
    Just True -> do
        tmFst <- newMetaTerm
                   (Just parent)
                   --(eqDeg :: Degree sys _)
                   (VarFromCtx <$> dmu :\\ gamma)
                   (_segment'content $ binding'segment $ sigmaBinding)
                   MetaBlocked
                   "Infer first projection."
        tmSnd <- newMetaTerm
                   (Just parent)
                   --(eqDeg :: Degree sys _)
                   gamma
                   (Type $ substLast2 tmFst $ binding'body sigmaBinding)
                   MetaBlocked
                   "Infer second projection."
        return $ Just $ Just $ Expr2 $ TermCons $ Pair sigmaBinding tmFst tmSnd
    Just False -> return $ Just Nothing
    Nothing -> return $ Nothing
etaExpand parent gamma t (BoxType boxSeg) = do
  let dgamma' = ctx'mode gamma
  let dgamma = unVarFromCtx <$> dgamma'
  let dmu = _segment'modty $ boxSeg
  allowsEta parent (crispModedModality dgamma' :\\ gamma) dmu dgamma "Need to know if eta is allowed." >>= \case
    Just True -> do
      let ty = Type $ Expr2 $ TermCons $ ConsUniHS $ BoxType boxSeg
      tmUnbox <- newMetaTerm
                   (Just parent)
                   --(eqDeg :: Degree sys _)
                   (VarFromCtx <$> dmu :\\ gamma)
                   (_segment'content boxSeg)
                   MetaBlocked
                   "Infer box content."
      return $ Just $ Just $ Expr2 $ TermCons $ ConsBox boxSeg tmUnbox
    Just False -> return $ Just Nothing
    Nothing -> return $ Nothing
etaExpand parent gamma t UnitType = return $ Just $ Just $ Expr2 $ TermCons $ ConsUnit
etaExpand parent gamma t (UniHS _) = return $ Just $ Nothing
etaExpand parent gamma t EmptyType = return $ Just $ Nothing
etaExpand parent gamma t NatType = return $ Just $ Nothing
etaExpand parent gamma t (EqType _ _ _) = return $ Just $ Nothing

checkEtaForNormalType :: forall sys tc v .
  (SysTC sys, MonadTC sys tc, DeBruijnLevel v) =>
  Constraint sys ->
  Ctx Type sys v Void ->
  Term sys v ->
  UniHSConstructor sys v ->
  tc Bool
checkEtaForNormalType parent gamma t ty = do
  maybeMaybeTExpanded <- etaExpand parent gamma t ty
  let ty' = hs2type ty
  case maybeMaybeTExpanded of
    Nothing -> tcBlock parent $ "Need to know if this type has eta."
    Just Nothing -> return False
    Just (Just tExpanded) -> do
      addNewConstraint
        (JudTermRel
          (Eta True)
          (eqDeg :: Degree sys _)
          (duplicateCtx gamma)
          (Twice2 t tExpanded)
          (Twice2 ty' ty')
        )
        (Just parent)
        "Eta-expand"
      return True

checkEta ::
  (SysTC sys, MonadTC sys tc, DeBruijnLevel v) =>
  Constraint sys ->
  Ctx Type sys v Void ->
  Term sys v ->
  Type sys v ->
  tc Bool
checkEta parent gamma t ty = do
  (whnTy, metas) <- runWriterT $ whnormalizeType parent gamma ty "Normalizing type."
  case metas of
    [] -> do
      parent' <- defConstraint
                   (JudEta gamma t whnTy)
                   (Just parent)
                   "Weak-head-normalized type."
      case unType whnTy of
        Var2 v -> return False
        Expr2 whnTyNV -> case whnTyNV of
          TermCons (ConsUniHS whnTyCons) -> checkEtaForNormalType parent' gamma t whnTyCons
          TermCons _ -> tcFail parent' $ "Type is not a type."
          TermElim _ _ _ _ -> return False
          TermMeta MetaBlocked _ _ _ -> unreachable
          TermMeta MetaNeutral _ _ _ -> tcBlock parent "Need to weak-head-normalize type before I can eta-expand."
          TermWildcard -> unreachable
          TermQName _ _ -> unreachable
          TermAlreadyChecked _ _ -> unreachable
          TermAlgorithm _ _ -> unreachable
          TermSys whnSysTy -> checkEtaWHNSysTy parent' gamma t whnSysTy
          TermProblem _ -> tcFail parent' $ "Nonsensical type."
    _ -> tcBlock parent "Need to weak-head-normalize type before I can eta-expand."

--------------------------------------------------------
-- MAYBE ETA IF SPECIFIED --
--------------------------------------------------------

tryToSolveMeta :: forall sys tc v .
  (SysTC sys, MonadTC sys tc, DeBruijnLevel v) =>
  Constraint sys ->
  Eta ->
  ModedDegree sys v ->
  Ctx (Twice2 Type) sys v Void ->
  MetaNeutrality -> Int -> [Term sys v] -> Maybe (Algorithm sys v) ->
  Term sys v ->
  Type sys v ->
  Type sys v ->
  [Int] ->
  [Int] ->
  (String -> tc ()) {-^ Either block or resort to eta-equality. -} ->
  tc ()
tryToSolveMeta parent eta deg gamma neutrality1 meta1 depcies1 maybeAlg1 t2 ty1 ty2 metasTy1 metasTy2 alternative = do
  let getVar2 :: Term sys v -> Maybe v
      getVar2 (Var2 v) = Just v
      getVar2 _ = Nothing
  let dgamma' = ctx'mode gamma
  let dgamma = unVarFromCtx <$> dgamma'
  case sequenceA $ getVar2 <$> depcies1 of
    -- Some dependency is not a variable
    Nothing -> alternative "Cannot solve meta-variable: it has non-variable dependencies."
    -- All dependencies are variables
    Just depcyVars -> do
      let (_, repeatedVars, _) = complex depcyVars
      case repeatedVars of
        -- Some variables occur twice
        _:_ -> alternative "Cannot solve meta-variable: it has undergone contraction of dependencies."
        -- All variables are unique
        [] -> solveMeta parent meta1 ( \ gammaOrig -> do
            -- Turn list of variables into a function mapping variables from gammaOrig to variables from gamma
            let subst = (depcyVars !!) . fromIntegral . (getDeBruijnLevel Proxy)
            let partialInv = join . fmap (forDeBruijnLevel Proxy . fromIntegral) . flip elemIndex depcyVars
            itIsEqDeg <- isEqDeg parent (crispModedModality dgamma' :\\ fstCtx gamma) (_degree'deg deg) dgamma
              "Need to know if I'm checking for equality"
            solution <- case itIsEqDeg of
              Just True ->
                   solveMetaImmediately parent
                     gammaOrig gamma subst partialInv t2 ty1 ty2 metasTy1 metasTy2 alternative
              _ -> if unEta eta
                   then do --Nothing <$ alternative "Let's try eta-expansion."
                     let t1 = Expr2 $ TermMeta neutrality1 meta1 (Compose depcies1) (Compose maybeAlg1)
                     etaHolds <- checkEta parent (fstCtx gamma) t1 ty1
                     if etaHolds
                       then Nothing <$ addConstraint parent
                       else solveMetaAgainstWHNF parent deg
                          gammaOrig gamma subst partialInv t2 ty1 ty2 metasTy1 metasTy2 $ tcBlock parent
                   else solveMetaAgainstWHNF parent deg
                          gammaOrig gamma subst partialInv t2 ty1 ty2 metasTy1 metasTy2 $ alternative
            case neutrality1 of
              MetaBlocked -> return solution
              MetaNeutral -> case solution of
                Just (Expr2 (TermCons c)) -> tcFail parent $
                  "Cannot instantiate neutral meta with a constructor. " ++
                  "(If the expected solution is an eta-expanded normal expression, then we've found a bug.)"
                  -- In the future (e.g. when you do neutral-implicit annotations), you may want to try and eta-contract c.
                  -- Note that `x > (f x .1 , f x ..2)` is not easy to eta-contract to `f`.
                  -- Best done using an eta-contraction judgement analogous to smart-elim judgement.
                _ -> return solution
          )
  
tryToSolveTerm :: forall sys tc v .
  (SysTC sys, MonadTC sys tc, DeBruijnLevel v) =>
  Constraint sys ->
  Eta ->
  ModedDegree sys v ->
  Ctx (Twice2 Type) sys v Void ->
  Term sys v {-^ Blocked. -} ->
  Term sys v ->
  Type sys v ->
  Type sys v ->
  [Int] ->
  [Int] ->
  (String -> tc ()) ->
  tc ()
tryToSolveTerm parent eta deg gamma t1 t2 ty1 ty2 metasTy1 metasTy2 alternative = case t1 of
  (Expr2 (TermMeta neutrality1 meta1 (Compose depcies1) (Compose maybeAlg1))) ->
    tryToSolveMeta parent eta deg gamma neutrality1 meta1 depcies1 maybeAlg1 t2 ty1 ty2 metasTy1 metasTy2 alternative
  _ -> alternative "Cannot solve relation: one side is blocked on a meta-variable."

