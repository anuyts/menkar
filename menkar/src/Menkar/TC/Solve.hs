{-# LANGUAGE IncoherentInstances #-}

module Menkar.TC.Solve where

import Menkar.System.Fine
import Menkar.System.WHN
import Menkar.System.TC
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
  Degree sys v ->
  Ctx Type sys vOrig Void ->
  Ctx (Twice2 Type) sys v Void ->
  (vOrig -> v) ->
  (v -> Maybe vOrig) ->
  Term sys v ->
  Type sys v ->
  Type sys v ->
  Bool ->
  String ->
  tc (Term sys vOrig)
newRelatedMetaTerm parent deg gammaOrig gamma subst partialInv t2 ty1 ty2 etaFlag reason = do
      t1orig <- newMetaTermNoCheck (Just parent) gammaOrig etaFlag Nothing reason
      let t1 = subst <$> t1orig
      addNewConstraint
        (JudTermRel deg gamma (Twice2 t1 t2) (Twice2 ty1 ty2))
        (Just parent)
        reason
      return t1orig

newRelatedMetaType :: forall sys tc v vOrig .
  (SysTC sys, MonadTC sys tc, Eq v, DeBruijnLevel v, DeBruijnLevel vOrig) =>
  Constraint sys ->
  Degree sys v ->
  Ctx Type sys vOrig Void ->
  Ctx (Twice2 Type) sys v Void ->
  (vOrig -> v) ->
  (v -> Maybe vOrig) ->
  Type sys v ->
  String ->
  tc (Type sys vOrig)
newRelatedMetaType parent deg gammaOrig gamma subst partialInv ty2 reason = do
      ty1orig <- Type <$> newMetaTermNoCheck (Just parent) gammaOrig False Nothing reason
      let ty1 = subst <$> ty1orig
      addNewConstraint
        (JudTypeRel deg gamma (Twice2 ty1 ty2))
        (Just parent)
        reason
      return ty1orig

--------------------------

newRelatedSegment :: (SysTC sys, MonadTC sys tc, Eq v, DeBruijnLevel v, DeBruijnLevel vOrig) =>
  Constraint sys ->
  Degree sys v ->
  Ctx Type sys vOrig Void ->
  Ctx (Twice2 Type) sys v Void ->
  (vOrig -> v) ->
  (v -> Maybe vOrig) ->
  Segment Type sys v ->
  tc (Segment Type sys vOrig)
newRelatedSegment parent deg gammaOrig gamma subst partialInv segment2 = do
  let dmu2 = _decl'modty segment2
  dmu1orig <- newRelatedMetaModedModality
                parent
                (crispModedModality :\\ gammaOrig)
                (crispModedModality :\\ gamma)
                subst partialInv dmu2
                (unVarFromCtx <$> ctx'mode gamma)
                "Inferring segment modality."
  let dmu1 = subst <$> dmu1orig
  let ty2 = _decl'content segment2
  ty1orig <- newRelatedMetaType
               parent
               (divDeg dmu1 deg)
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
  Degree sys v ->
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
                 (VarWkn <$> deg)
                 (gammaOrig :.. VarFromCtx <$> segment1orig)
                 (gamma :.. VarFromCtx <$> over decl'content (\dom2 -> Twice2 dom1 dom2) segment2)
                 (fmap subst)
                 fmapPartialInv
                 (binding'body binding2)
                 tyBody1
                 tyBody2
                 True
                 "Inferring body."
  return $ Binding segment1orig body1orig

------------------------------------

newRelatedUniHSConstructor :: (SysTC sys, MonadTC sys tc, Eq v, DeBruijnLevel v, DeBruijnLevel vOrig) =>
  Constraint sys ->
  Degree sys v ->
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
        newRelatedMetaTerm parent deg gammaOrig gamma subst partialInv tL2 tyAmbient1 tyAmbient2
          True "Inferring left equand."
      tR1orig <-
        newRelatedMetaTerm parent deg gammaOrig gamma subst partialInv tR2 tyAmbient1 tyAmbient2
          True "Inferring right equand."
      return $ EqType tyAmbient1orig tL1orig tR1orig

newRelatedConstructorTerm :: forall sys tc v vOrig .
  (SysTC sys, MonadTC sys tc, Eq v, DeBruijnLevel v, DeBruijnLevel vOrig) =>
  Constraint sys ->
  Degree sys v ->
  Ctx Type sys vOrig Void ->
  Ctx (Twice2 Type) sys v Void ->
  (vOrig -> v) ->
  (v -> Maybe vOrig) ->
  ConstructorTerm sys v ->
  Type sys v ->
  Type sys v ->
  [Int] ->
  [Int] ->
  tc (ConstructorTerm sys vOrig)
newRelatedConstructorTerm parent deg gammaOrig gamma subst partialInv t2 ty1 ty2 metasTy1 metasTy2 =
  case t2 of
    ConsUniHS c2 -> do
      c1orig <- newRelatedUniHSConstructor parent deg gammaOrig gamma subst partialInv c2
      return $ ConsUniHS $ c1orig
    Lam binding2 -> do
      case (metasTy1, ty1, metasTy2, ty2) of
        ([], Type (Expr2 (TermCons (ConsUniHS (Pi piBinding1)))),
         [], Type (Expr2 (TermCons (ConsUniHS (Pi piBinding2))))) -> do
            let cod1 = Type $ binding'body piBinding1
            let cod2 = Type $ binding'body piBinding2
            binding1orig <- newRelatedBinding parent deg gammaOrig gamma subst partialInv binding2 cod1 cod2
            return $ Lam binding1orig
        ([], _, [], _) -> tcFail parent "Terms are presumed to be well-typed."
        (_ , _, _ , _) -> tcBlock parent "Need to know codomains of function types."
    Pair sigmaBindingPair2 tmFst2 tmSnd2 -> do
      case (metasTy1, ty1, metasTy2, ty2) of
        ([], Type (Expr2 (TermCons (ConsUniHS (Sigma sigmaBinding1)))),
         [], Type (Expr2 (TermCons (ConsUniHS (Sigma sigmaBinding2))))) -> do
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
            tmFst1orig <- newRelatedMetaTerm parent
                            (divDeg dmuPair2 deg)
                            (VarFromCtx <$> dmuPair1orig :\\ gammaOrig)
                            (VarFromCtx <$> dmuPair2 :\\ gamma)
                            subst partialInv tmFst2 tyFst1 tyFst2
                            True "Inferring first component."
            let tmFst1 = subst <$> tmFst1orig
            ---------
            let tySnd1 = substLast2 tmFst1 $ Type $ binding'body sigmaBinding1
            let tySnd2 = substLast2 tmFst2 $ Type $ binding'body sigmaBinding2
            ---------
            tmSnd1orig <- newRelatedMetaTerm parent deg gammaOrig gamma subst partialInv tmSnd2 tySnd1 tySnd2
                            True "Inferring second component."
            let tmSnd1 = subst <$> tmSnd1orig
            ---------
            return $ Pair sigmaBindingPair1orig tmFst1orig tmSnd1orig
        ([], _, [], _) -> tcFail parent "Terms are presumed to be well-typed."
        (_, _, _, _) -> tcBlock parent "Need to know domains and codomains of Sigma-types."
    ConsUnit -> return ConsUnit
    ConsBox boxSegTerm2 tmUnbox2 -> do
      case (metasTy1, ty1, metasTy2, ty2) of
        ([], Type (Expr2 (TermCons (ConsUniHS (BoxType boxSeg1)))),
         [], Type (Expr2 (TermCons (ConsUniHS (BoxType boxSeg2))))) -> do
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
            tmUnbox1orig <- newRelatedMetaTerm parent
                            (divDeg dmuTerm2 deg)
                            (VarFromCtx <$> dmuTerm1orig :\\ gammaOrig)
                            (VarFromCtx <$> dmuTerm2 :\\ gamma)
                            subst partialInv tmUnbox2 tyUnbox1 tyUnbox2
                            True "Inferring box content."
            let tmUnbox1 = subst <$> tmUnbox1orig
            ---------
            return $ ConsBox boxSegTerm1orig tmUnbox1orig
        ([], _, [], _) -> tcFail parent "Terms are presumed to be well-typed."
        (_, _, _, _) -> tcBlock parent "Need to know content types of box types."
    ConsZero -> return ConsZero
    ConsSuc t2 -> do
      let nat = hs2type $ NatType
      t1orig <- newRelatedMetaTerm parent deg gammaOrig gamma subst partialInv t2 nat nat False "Inferring predecessor."
      return $ ConsSuc t1orig
    ConsRefl -> return ConsRefl

------------------------------------

newRelatedDependentEliminator :: forall sys tc v vOrig .
  (SysTC sys, MonadTC sys tc, Eq v, DeBruijnLevel v, DeBruijnLevel vOrig) =>
  Constraint sys ->
  Degree sys v ->
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
            parent
            (VarWkn . VarWkn <$> deg)
            (gammaOrig :.. VarFromCtx <$> segFst1orig :.. VarFromCtx <$> segSnd1orig)
            (gamma     :.. VarFromCtx <$> segFst      :.. VarFromCtx <$> segSnd)
            (fmap $ fmap subst)
            (sequenceA . fmap sequenceA . (fmap $ fmap partialInv))
            t2 ty1 ty2
            True
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
            parent
            (VarWkn <$> deg)
            (gammaOrig :.. VarFromCtx <$> segUnbox1orig)
            (gamma     :.. VarFromCtx <$> segUnbox)
            (fmap subst)
            (sequenceA . fmap partialInv)
            t2 ty1 ty2
            True
            "Inferring box clause."
          )
        return $ ElimBox boxClause1orig
      (_, _) -> unreachable
    ElimEmpty -> return ElimEmpty
    ElimNat clauseZero2 clauseSuc2 -> do
      let tyCZ1 = substLast2 (Expr2 $ TermCons $ ConsZero :: Term sys _) $ _namedBinding'body motive1
      let tyCZ2 = substLast2 (Expr2 $ TermCons $ ConsZero :: Term sys _) $ _namedBinding'body motive2
      clauseZero1orig <-
        newRelatedMetaTerm parent deg gammaOrig gamma subst partialInv clauseZero2 tyCZ1 tyCZ2
          False "Inferring zero clause."
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
          parent
          (VarWkn . VarWkn <$> deg)
          (gammaOrig :.. VarFromCtx <$> segPred1orig :.. VarFromCtx <$> segHyp1orig)
          (gamma     :.. VarFromCtx <$> segPred      :.. VarFromCtx <$> segHyp)
          (fmap $ fmap subst)
          (sequenceA . fmap sequenceA . (fmap $ fmap partialInv))
          t2 tyCS1 tyCS2
          True
          "Inferring pair clause."
      return $ ElimNat clauseZero1orig clauseSuc1orig

newRelatedEliminator :: forall sys tc v vOrig .
  (SysTC sys, MonadTC sys tc, Eq v, DeBruijnLevel v, DeBruijnLevel vOrig) =>
  Constraint sys ->
  Degree sys v ->
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
                      parent
                      (divDeg dmuPi1 deg)
                      (VarFromCtx <$> dmuPi1orig :\\ gammaOrig)
                      (VarFromCtx <$> dmuPi1     :\\ gamma)
                      subst
                      partialInv
                      arg2
                      (_segment'content $ binding'segment piBinding1)
                      (_segment'content $ binding'segment piBinding2)
                      True
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
        crefl1orig <- newRelatedMetaTerm parent deg gammaOrig gamma subst partialInv
                        crefl2
                        (substLast2 tL1 $ substLast2 refl $ _namedBinding'body $ _namedBinding'body motive1)
                        (substLast2 tL2 $ substLast2 refl $ _namedBinding'body $ _namedBinding'body motive2)
                        True
                        "Inferring refl clause."
        return $ ElimEq motive1orig crefl1orig
      (_, _) -> unreachable

------------------------------------

{-| Precondition: @partialInv . subst = Just@.
-}
solveMetaAgainstWHNF :: (SysTC sys, MonadTC sys tc, Eq v, DeBruijnLevel v, DeBruijnLevel vOrig) =>
  Constraint sys ->
  Degree sys v ->
  Ctx Type sys vOrig Void ->
  Ctx (Twice2 Type) sys v Void ->
  (vOrig -> v) ->
  (v -> Maybe vOrig) ->
  Term sys v ->
  Type sys v ->
  Type sys v ->
  [Int] ->
  [Int] ->
  tc (Term sys vOrig)
solveMetaAgainstWHNF parent deg gammaOrig gamma subst partialInv t2 ty1 ty2 metasTy1 metasTy2 =
  case t2 of
    Var2 v -> case partialInv v of
      Nothing -> tcBlock parent "Cannot instantiate metavariable with a variable that it does not depend on."
      Just u -> return $ Var2 u
    Expr2 t2 -> case t2 of
      TermCons c2 -> do
        c1orig <- newRelatedConstructorTerm parent deg gammaOrig gamma subst partialInv c2 ty1 ty2 metasTy1 metasTy2
        return $ Expr2 $ TermCons $ c1orig
      TermElim dmu2 eliminee2 tyEliminee2 eliminator2 -> do
        dmu1orig <- newRelatedMetaModedModality
                      parent
                      (crispModedModality :\\ gammaOrig)
                      (crispModedModality :\\ gamma)
                      subst
                      partialInv
                      dmu2
                      (unVarFromCtx <$> ctx'mode gamma)
                      "Inferring elimination mode and modality."
        let dmu1 = subst <$> dmu1orig
        tyEliminee1orig <- newRelatedUniHSConstructor
                             parent
                             (divDeg dmu1 deg)
                             (VarFromCtx <$> dmu1orig :\\ gammaOrig)
                             (VarFromCtx <$> dmu1 :\\ gamma)
                             subst
                             partialInv
                             tyEliminee2
        let tyEliminee1 = subst <$> tyEliminee1orig
        eliminee1orig <- newRelatedMetaTerm
                             parent
                             (divDeg dmu1 deg)
                             (VarFromCtx <$> dmu1orig :\\ gammaOrig)
                             (VarFromCtx <$> dmu1 :\\ gamma)
                             subst
                             partialInv
                             eliminee2
                             (Type $ Expr2 $ TermCons $ ConsUniHS $ tyEliminee1)
                             (Type $ Expr2 $ TermCons $ ConsUniHS $ tyEliminee2)
                             False
                               {- This is the reason this flag exists:
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
        return $ Expr2 $ TermElim dmu1orig eliminee1orig tyEliminee1orig eliminator1orig
      TermMeta _ _ _ _ -> unreachable
      TermWildcard -> unreachable
      TermQName _ _ -> unreachable
      TermAlgorithm _ _ -> unreachable
      TermProblem _ -> do
        tcFail parent "Nonsensical term."
      TermSys t2 -> newRelatedSysTerm parent deg gammaOrig gamma subst partialInv t2 ty1 ty2 metasTy1 metasTy2

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
  tc (Term sys vOrig)
solveMetaImmediately parent gammaOrig gamma subst partialInv t2 ty1 ty2 metasTy1 metasTy2 = do
  -- Try to write t2 in gammaOrig
  let maybeT2orig = sequenceA $ partialInv <$> t2
  case maybeT2orig of
    -- If it works, return that.
    Just t2orig -> return t2orig
    -- If t2 contains variables not in gammaOrig: solve against WHNF
    Nothing -> solveMetaAgainstWHNF parent eqDeg gammaOrig gamma subst partialInv t2 ty1 ty2 metasTy1 metasTy2

------------------------------------

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
  -- CMODE require that forall u . dmuOrig u <= dmu (subst u)
  let condition :: vOrig -> tc (Maybe Bool)
      condition u = leqMod
        (subst <$> (modality'dom $ dmuOrig u))
        (subst . unVarFromCtx <$> ctx'mode gammaOrig)
        (subst <$> (modality'mod $ dmuOrig u))
        (modality'mod $ dmu $ subst u)
  fmap (fmap and . sequenceA) $ sequenceA $ condition <$> listAll Proxy

------------------------------------

tryToSolveMeta :: (SysTC sys, MonadTC sys tc, Eq v, DeBruijnLevel v) =>
  Constraint sys ->
  Degree sys v ->
  Ctx (Twice2 Type) sys v Void ->
  Int ->
  [Term sys v] ->
  Term sys v ->
  Type sys v ->
  Type sys v ->
  [Int] ->
  [Int] ->
  tc ()
tryToSolveMeta parent deg gamma meta depcies t2 ty1 ty2 metasTy1 metasTy2 = do
  let getVar2 :: Term sys v -> Maybe v
      getVar2 (Var2 v) = Just v
      getVar2 _ = Nothing
  case sequenceA $ getVar2 <$> depcies of
    -- Some dependency is not a variable
    Nothing -> tcBlock parent "Cannot solve meta-variable: it has non-variable dependencies."
    -- All dependencies are variables
    Just depcyVars -> do
      let (_, repeatedVars, _) = complex depcyVars
      case repeatedVars of
        -- Some variables occur twice
        _:_ -> tcBlock parent "Cannot solve meta-variable: it has undergone contraction of dependencies."
        -- All variables are unique
        [] -> solveMeta parent meta ( \ gammaOrig -> do
            -- Turn list of variables into a function mapping variables from gammaOrig to variables from gamma
            let depcySubst = (depcyVars !!) . fromIntegral . (getDeBruijnLevel Proxy)
            -- Check if the meta is pure
            isPure <- checkMetaPure parent gammaOrig (fstCtx gamma) depcySubst ty1
            case isPure of
              -- If so, weak-head-solve it
              Just True -> do
                let depcySubstInv = join . fmap (forDeBruijnLevel Proxy . fromIntegral) . flip elemIndex depcyVars
                isEqDeg (unVarFromCtx <$> ctx'mode gamma) deg >>= \case
                  Just True ->
                       solveMetaImmediately parent     gammaOrig gamma depcySubst depcySubstInv t2 ty1 ty2 metasTy1 metasTy2
                  _ -> solveMetaAgainstWHNF parent deg gammaOrig gamma depcySubst depcySubstInv t2 ty1 ty2 metasTy1 metasTy2
              -- otherwise, block and fail to solve it (we need to give a return value to solveMeta).
              _ -> tcBlock parent
                "Cannot solve meta-variable: modalities in current context are not obviously as strong as in original context."
          )

tryToSolveTerm :: (SysTC sys, MonadTC sys tc, Eq v, DeBruijnLevel v) =>
  Constraint sys ->
  Degree sys v ->
  Ctx (Twice2 Type) sys v Void ->
  Term sys v ->
  Term sys v ->
  [Int] ->
  Type sys v ->
  Type sys v ->
  [Int] ->
  [Int] ->
  tc ()
tryToSolveTerm parent deg gamma tBlocked t2 metasBlocked tyBlocked ty2 metasTyBlocked metasTy2 = case tBlocked of
  -- tBlocked should be a meta
  (Expr2 (TermMeta etaFlag meta depcies alg)) ->
    tryToSolveMeta parent deg gamma meta (getCompose depcies) t2 tyBlocked ty2 metasTyBlocked metasTy2
  -- if tBlocked is not a meta, then we should just block on its submetas
  _ -> tcBlock parent "Cannot solve relation: one side is blocked on a meta-variable."
