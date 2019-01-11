{-# LANGUAGE IncoherentInstances #-}

module Menkar.TC.Inference.Solve where

import Menkar.Fine.Syntax
import Menkar.Basic.Context
import Menkar.Fine.Context
import Menkar.Fine.Judgement
import Menkar.Fine.Multimode
import Menkar.Fine.LookupQName
import qualified Menkar.Raw.Syntax as Raw
import Menkar.TC.Monad
import Control.Exception.AssertFalse
import Menkar.Fine.WHNormalize

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
forceSolveMeta :: (MonadTC mode modty rel tc, Eq v, DeBruijnLevel v, Traversable t) =>
  Constraint mode modty rel ->
  rel v ->
  Ctx Type mode modty vOrig Void ->
  Ctx (Pair3 Type) mode modty v Void ->
  (vOrig -> v) ->
  (v -> Maybe vOrig) ->
  Int ->
  Type mode modty v ->
  t v ->
  tc (Maybe (t vOrig))
forceSovleMeta parent deg gammaOrig gamma subst partialInv meta tyMeta t = do
  let maybeTOrig = sequenceA $ partialInv <$> t
  case maybeTOrig of
    
-}

newRelatedMetaTerm :: (MonadTC mode modty rel tc, Eq v, DeBruijnLevel v, DeBruijnLevel vOrig) =>
  Constraint mode modty rel ->
  rel v ->
  Ctx Type mode modty vOrig Void ->
  Ctx (Pair3 Type) mode modty v Void ->
  (vOrig -> v) ->
  (v -> Maybe vOrig) ->
  Term mode modty v ->
  Type mode modty v ->
  Type mode modty v ->
  String ->
  tc (Term mode modty vOrig)
newRelatedMetaTerm parent deg gammaOrig gamma subst partialInv t2 ty1 ty2 reason = do
  let maybeDegOrig = sequenceA $ partialInv <$> deg
  case maybeDegOrig of
    Nothing -> tcBlock parent "Cannot weak-head-solve this equation here: the degree of relatedness has dependencies that the meta-variable does not depend on."
    Just degOrig -> do
      t1orig <- newMetaTermNoCheck (Just parent) degOrig gammaOrig reason
      let t1 = subst <$> t1orig
      addNewConstraint
        (JudTermRel deg gamma (Pair3 t1 t2) (Pair3 ty1 ty2))
        (Just parent)
        reason
      return t1orig

newRelatedMetaType :: (MonadTC mode modty rel tc, Eq v, DeBruijnLevel v, DeBruijnLevel vOrig) =>
  Constraint mode modty rel ->
  rel v ->
  Ctx Type mode modty vOrig Void ->
  Ctx (Pair3 Type) mode modty v Void ->
  (vOrig -> v) ->
  (v -> Maybe vOrig) ->
  Type mode modty v ->
  String ->
  tc (Type mode modty vOrig)
newRelatedMetaType parent deg gammaOrig gamma subst partialInv ty2 reason = do
  let maybeDegOrig = sequenceA $ partialInv <$> deg
  case maybeDegOrig of
    Nothing -> tcBlock parent "Cannot weak-head-solve this equation here: the degree of relatedness has dependencies that the meta-variable does not depend on."
    Just degOrig -> do
      ty1orig <- Type <$> newMetaTermNoCheck (Just parent) degOrig gammaOrig reason
      let ty1 = subst <$> ty1orig
      addNewConstraint
        (JudTypeRel deg gamma (Pair3 ty1 ty2))
        (Just parent)
        reason
      return ty1orig

--------------------------

newRelatedSegment :: (MonadTC mode modty rel tc, Eq v, DeBruijnLevel v, DeBruijnLevel vOrig) =>
  Constraint mode modty rel ->
  rel v ->
  Ctx Type mode modty vOrig Void ->
  Ctx (Pair3 Type) mode modty v Void ->
  (vOrig -> v) ->
  (v -> Maybe vOrig) ->
  Segment Type mode modty v ->
  tc (Segment Type mode modty vOrig)
newRelatedSegment parent deg gammaOrig gamma subst partialInv segment2 = do
  let dmu2 = _decl'modty segment2
  -- CMODE: dmu1orig <- newRelatedModedModality dmu2 
  let dmu1orig = wildModedModality
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

newRelatedBinding :: (MonadTC mode modty rel tc, Eq v, DeBruijnLevel v, DeBruijnLevel vOrig) =>
  Constraint mode modty rel ->
  rel v ->
  Ctx Type mode modty vOrig Void ->
  Ctx (Pair3 Type) mode modty v Void ->
  (vOrig -> v) ->
  (v -> Maybe vOrig) ->
  Binding Type Term mode modty v ->
  Type mode modty (VarExt v) ->
  Type mode modty (VarExt v) ->
  tc (Binding Type Term mode modty vOrig)
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
                 (gamma :.. VarFromCtx <$> over decl'content (\dom2 -> Pair3 dom1 dom2) segment2)
                 (fmap subst)
                 fmapPartialInv
                 (binding'body binding2)
                 tyBody1
                 tyBody2
                 "Inferring body."
  return $ Binding segment1orig body1orig

------------------------------------

solveMetaAgainstUniHSConstructor :: (MonadTC mode modty rel tc, Eq v, DeBruijnLevel v, DeBruijnLevel vOrig) =>
  Constraint mode modty rel ->
  rel v ->
  Ctx Type mode modty vOrig Void ->
  Ctx (Pair3 Type) mode modty v Void ->
  (vOrig -> v) ->
  (v -> Maybe vOrig) ->
  UniHSConstructor mode modty v ->
  tc (UniHSConstructor mode modty vOrig)
solveMetaAgainstUniHSConstructor parent deg gammaOrig gamma subst partialInv t2 = do
  let d1orig = unVarFromCtx <$> ctx'mode gammaOrig
  case t2 of
    UniHS d2 {-lvl2-} -> do
      --let nat = Type $ Expr3 $ TermCons $ ConsUniHS $ NatType
      --lvl1orig <- newRelatedMetaTerm parent topDeg gammaOrig gamma subst partialInv lvl2 nat nat "Inferring level."
                --newMetaTermNoCheck (Just parent) topDeg gammaOrig nat "Inferring level."
      return $ UniHS d1orig --lvl1orig
    Pi binding2 -> do
      let uni = hs2type $ UniHS (unVarFromCtx <$> ctx'mode gamma) --(Expr3 $ TermWildcard)
      binding1orig <-
        newRelatedBinding parent deg gammaOrig gamma subst partialInv binding2 (VarWkn <$> uni) (VarWkn <$> uni)
      return $ Pi $ binding1orig
    Sigma binding2 -> do
      let uni = hs2type $ UniHS (unVarFromCtx <$> ctx'mode gamma) --(Expr3 $ TermWildcard)
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
        newRelatedMetaTerm parent deg gammaOrig gamma subst partialInv tL2 tyAmbient1 tyAmbient2 "Inferring left equand."
      tR1orig <-
        newRelatedMetaTerm parent deg gammaOrig gamma subst partialInv tR2 tyAmbient1 tyAmbient2 "Inferring right equand."
      return $ EqType tyAmbient1orig tL1orig tR1orig

solveMetaAgainstConstructorTerm :: (MonadTC mode modty rel tc, Eq v, DeBruijnLevel v, DeBruijnLevel vOrig) =>
  Constraint mode modty rel ->
  rel v ->
  Ctx Type mode modty vOrig Void ->
  Ctx (Pair3 Type) mode modty v Void ->
  (vOrig -> v) ->
  (v -> Maybe vOrig) ->
  ConstructorTerm mode modty v ->
  Type mode modty v ->
  Type mode modty v ->
  [Int] ->
  [Int] ->
  tc (ConstructorTerm mode modty vOrig)
solveMetaAgainstConstructorTerm parent deg gammaOrig gamma subst partialInv t2 ty1 ty2 metasTy1 metasTy2 =
  case t2 of
    ConsUniHS c2 -> do
      c1orig <- solveMetaAgainstUniHSConstructor parent deg gammaOrig gamma subst partialInv c2
      return $ ConsUniHS $ c1orig
    Lam binding2 -> do
      case (metasTy1, ty1, metasTy2, ty2) of
        ([], Type (Expr3 (TermCons (ConsUniHS (Pi piBinding1)))),
         [], Type (Expr3 (TermCons (ConsUniHS (Pi piBinding2))))) -> do
            let cod1 = Type $ binding'body piBinding1
            let cod2 = Type $ binding'body piBinding2
            binding1orig <- newRelatedBinding parent deg gammaOrig gamma subst partialInv binding2 cod1 cod2
            return $ Lam binding1orig
        ([], _, [], _) -> tcFail parent "Terms are presumed to be well-typed."
        (_, _, _, _) -> tcBlock parent "Need to know codomains of function types."
    Pair sigmaBinding2 tmFst2 tmSnd2 -> do
      case (metasTy1, ty1, metasTy2, ty2) of
        ([], Type (Expr3 (TermCons (ConsUniHS (Sigma sigmaBinding1)))),
         [], Type (Expr3 (TermCons (ConsUniHS (Sigma sigmaBinding2))))) -> do
            let tyFst1 = _segment'content $ binding'segment sigmaBinding1
            let tyFst2 = _segment'content $ binding'segment sigmaBinding2
            let dmu1 = _segment'modty $ binding'segment sigmaBinding1
            -- CMODE: figure out modality
            let dmu1orig = wildModedModality
            tmFst1orig <- newRelatedMetaTerm parent (divDeg dmu1orig deg) (VarFromCtx <$> dmu1orig :\\ gammaOrig)
                            (VarFromCtx <$> dmu1 :\\ gamma) subst partialInv tmFst2 tyFst1 tyFst2
                            "Inferring first component."
            let tmFst1 = subst <$> tmFst1orig
            let tySnd1 = substLast3 tmFst1 $ Type $ binding'body sigmaBinding1
            let tySnd2 = substLast3 tmFst2 $ Type $ binding'body sigmaBinding2
            -- CMODE: deg should probably live in vOrig
            let degOrig = fromMaybe unreachable $ sequenceA $ partialInv <$> deg
            tyFst1orig <- newMetaTermNoCheck (Just parent) degOrig gammaOrig "Inferring type of first component."
            let sigmaSeg1orig = Declaration
                                  (_decl'name $ binding'segment $ sigmaBinding1)
                                  dmu1orig
                                  Explicit -- CMODE
                                  (Type tyFst1orig)
            tySnd1orig <- newMetaTermNoCheck (Just parent) (VarWkn <$> degOrig)
                               (gammaOrig :.. VarFromCtx <$> sigmaSeg1orig) "Inferring type of second component."
            let sigmaBinding1orig = Binding sigmaSeg1orig tySnd1orig
            tmSnd1orig <- newRelatedMetaTerm parent deg gammaOrig gamma subst partialInv tmSnd2 tySnd1 tySnd2
                            "Inferring second component."
            return $ Pair sigmaBinding1orig tmFst1orig tmSnd1orig
        ([], _, [], _) -> tcFail parent "Terms are presumed to be well-typed."
        (_, _, _, _) -> tcBlock parent "Need to know domains and codomains of Sigma-types."
    ConsUnit -> return ConsUnit
    ConsBox boxSeg tmUnbox2 -> do
      case (metasTy1, ty1, metasTy2, ty2) of
        ([], Type (Expr3 (TermCons (ConsUniHS (BoxType boxSeg1)))),
         [], Type (Expr3 (TermCons (ConsUniHS (BoxType boxSeg2))))) -> do
            let tyUnbox1 = _segment'content boxSeg1
            let tyUnbox2 = _segment'content boxSeg2
            let dmu1 = _segment'modty boxSeg1
            -- CMODE: figure out modality
            let dmu1orig = wildModedModality
            tmUnbox1orig <- newRelatedMetaTerm parent (divDeg dmu1orig deg) (VarFromCtx <$> dmu1orig :\\ gammaOrig)
                            (VarFromCtx <$> dmu1 :\\ gamma) subst partialInv tmUnbox2 tyUnbox1 tyUnbox2
                            "Inferring box content."
            let tmUnbox1 = subst <$> tmUnbox1orig
            -- CMODE: deg should probably live in vOrig
            let degOrig = fromMaybe unreachable $ sequenceA $ partialInv <$> deg
            tyUnbox1orig <- newMetaTermNoCheck (Just parent) degOrig gammaOrig "Inferring type of box content."
            let boxSeg1orig = Declaration
                                  (_decl'name $ boxSeg1)
                                  dmu1orig
                                  Explicit -- CMODE
                                  (Type tyUnbox1orig)
            return $ ConsBox boxSeg1orig tmUnbox1orig
        ([], _, [], _) -> tcFail parent "Terms are presumed to be well-typed."
        (_, _, _, _) -> tcBlock parent "Need to know content types of box types."
    ConsZero -> return ConsZero
    ConsSuc t2 -> do
      let nat = Type $ Expr3 $ TermCons $ ConsUniHS $ NatType
      t1orig <- newRelatedMetaTerm parent deg gammaOrig gamma subst partialInv t2 nat nat "Inferring predecessor."
      return $ ConsSuc t1orig
    ConsRefl -> return ConsRefl

------------------------------------

newRelatedDependentEliminator :: forall mode modty rel tc v vOrig .
  (MonadTC mode modty rel tc, Eq v, DeBruijnLevel v, DeBruijnLevel vOrig) =>
  Constraint mode modty rel ->
  rel v ->
  Ctx Type mode modty vOrig Void ->
  Ctx (Pair3 Type) mode modty v Void ->
  (vOrig -> v) ->
  (v -> Maybe vOrig) ->
  ModedModality mode modty vOrig {-^ Modality of elimination. -} ->
  Term mode modty vOrig ->
  Term mode modty v ->
  UniHSConstructor mode modty vOrig ->
  UniHSConstructor mode modty v ->
  NamedBinding Type mode modty vOrig ->
  NamedBinding Type mode modty v ->
  DependentEliminator mode modty v ->
  Type mode modty v ->
  Type mode modty v ->
  tc (DependentEliminator mode modty vOrig)
newRelatedDependentEliminator parent deg gammaOrig gamma subst partialInv
  dmu1orig
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
                            (Pair3
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
                            (Pair3
                              (Type $ binding'body sigmaBinding1)
                              (Type $ binding'body sigmaBinding2)
                            )
        let substPair' :: Binding Type Term _ _ _ -> VarExt _ -> Term _ _ (VarExt (VarExt _))
            substPair' sigmaBinding VarLast =
                Expr3 $ TermCons $ Pair (VarWkn . VarWkn <$> sigmaBinding) (Var3 $ VarWkn VarLast) (Var3 VarLast)
            substPair' sigmaBinding (VarWkn v) = Var3 $ VarWkn $ VarWkn $ v
            substPair :: Binding Type Term _ _ _ -> Type _ _ (VarExt _) -> Type _ _ (VarExt (VarExt _))
            substPair sigmaBinding = swallow . fmap (substPair' sigmaBinding)
        let ty1 = substPair sigmaBinding1 $ _namedBinding'body motive1
        let ty2 = substPair sigmaBinding2 $ _namedBinding'body motive2
        clausePair1orig <- flip namedBinding'body clausePair2 $ namedBinding'body $ \ t2 ->
          newRelatedMetaTerm
            parent
            (VarWkn . VarWkn <$> deg)
            (gammaOrig :.. VarFromCtx <$> segFst1orig :.. VarFromCtx <$> segSnd1orig)
            (gamma     :.. VarFromCtx <$> segFst      :.. VarFromCtx <$> segSnd)
            (fmap $ fmap subst)
            (sequenceA . fmap sequenceA . (fmap $ fmap partialInv))
            t2 ty1 ty2
            "Inferring pair clause."
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
                              (Pair3
                                (_segment'content boxSeg1)
                                (_segment'content boxSeg2)
                              )
        let substBox :: Segment Type mode modty v -> VarExt v -> Term mode modty (VarExt v)
            substBox boxSeg VarLast = Expr3 $ TermCons $ ConsBox (VarWkn <$> boxSeg) $ Var3 VarLast
            substBox boxSeg (VarWkn v) = Var3 $ VarWkn v
        let ty1 = swallow $ substBox boxSeg1 <$> _namedBinding'body motive1
        let ty2 = swallow $ substBox boxSeg1 <$> _namedBinding'body motive2
        boxClause1orig <- flip namedBinding'body boxClause2 $ \ t2 ->
          newRelatedMetaTerm
            parent
            (VarWkn <$> deg)
            (gammaOrig :.. VarFromCtx <$> segUnbox1orig)
            (gamma     :.. VarFromCtx <$> segUnbox)
            (fmap subst)
            (sequenceA . fmap partialInv)
            t2 ty1 ty2
            "Inferring box clause."
        return $ ElimBox boxClause1orig
      (_, _) -> unreachable
    ElimEmpty -> return ElimEmpty
    ElimNat clauseZero2 clauseSuc2 -> do
      let tyCZ1 = substLast3 (Expr3 $ TermCons $ ConsZero :: Term mode modty _) $ _namedBinding'body motive1
      let tyCZ2 = substLast3 (Expr3 $ TermCons $ ConsZero :: Term mode modty _) $ _namedBinding'body motive2
      clauseZero1orig <-
        newRelatedMetaTerm parent deg gammaOrig gamma subst partialInv clauseZero2 tyCZ1 tyCZ2
          "Inferring zero clause."
      -----------------
      let nat = (Type $ Expr3 $ TermCons $ ConsUniHS $ NatType)
      let namePred = _namedBinding'name clauseSuc2
      let nameHyp  = _namedBinding'name $ _namedBinding'body clauseSuc2
      let segPred1orig = Declaration (DeclNameSegment namePred) dmu1orig Explicit nat
      let segPred      = Declaration (DeclNameSegment namePred) dmu1     Explicit (Pair3 nat nat)
      let segHyp1orig = Declaration
                          (DeclNameSegment nameHyp)
                          (idModedModality $ VarWkn . unVarFromCtx <$> ctx'mode gammaOrig)
                          Explicit
                          (_namedBinding'body motive1orig)
      let segHyp      = Declaration
                          (DeclNameSegment nameHyp)
                          (idModedModality $ VarWkn . unVarFromCtx <$> ctx'mode gamma)
                          Explicit
                          (Pair3
                            (_namedBinding'body motive1)
                            (_namedBinding'body motive2)
                          )
      let substS :: VarExt v -> Term mode modty (VarExt (VarExt v))
          substS VarLast = Expr3 $ TermCons $ ConsSuc $ Var3 $ VarWkn VarLast
          substS (VarWkn v) = Var3 $ VarWkn $ VarWkn v
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
          "Inferring pair clause."
      return $ ElimNat clauseZero1orig clauseSuc1orig

newRelatedEliminator :: forall mode modty rel tc v vOrig .
  (MonadTC mode modty rel tc, Eq v, DeBruijnLevel v, DeBruijnLevel vOrig) =>
  Constraint mode modty rel ->
  rel v ->
  Ctx Type mode modty vOrig Void ->
  Ctx (Pair3 Type) mode modty v Void ->
  (vOrig -> v) ->
  (v -> Maybe vOrig) ->
  ModedModality mode modty vOrig {-^ Modality of elimination. -} ->
  Term mode modty vOrig ->
  Term mode modty v ->
  UniHSConstructor mode modty vOrig ->
  UniHSConstructor mode modty v ->
  Eliminator mode modty v ->
  Type mode modty v ->
  Type mode modty v ->
  tc (Eliminator mode modty vOrig)
newRelatedEliminator parent deg gammaOrig gamma subst partialInv
  dmu1orig
  eliminee1orig eliminee2
  tyEliminee1orig tyEliminee2
  eliminator2
  ty1 ty2 = do
  let dmu1 = subst <$> dmu1orig
  let tyEliminee1 = subst <$> tyEliminee1orig
  case eliminator2 of
    App arg2 -> case (tyEliminee1, tyEliminee2) of
      (Pi piBinding1, Pi piBinding2) -> do
        arg1orig <- newRelatedMetaTerm
                      parent
                      (divDeg dmu1 deg)
                      (VarFromCtx <$> dmu1orig :\\ gammaOrig)
                      (VarFromCtx <$> dmu1 :\\ gamma)
                      subst
                      partialInv
                      arg2
                      (_segment'content $ binding'segment piBinding1)
                      (_segment'content $ binding'segment piBinding2)
                      "Inferring argument."
        return $ App arg1orig
      (_, _) -> unreachable
    Fst -> return Fst
    Snd -> return Snd
    Unbox -> return Unbox
    ElimDep motive2 clauses2 -> do
      let seg1orig = Declaration (DeclNameSegment $ _namedBinding'name motive2) dmu1orig Explicit
                       (Type $ Expr3 $ TermCons $ ConsUniHS $ tyEliminee1orig)
      let seg      = Declaration (DeclNameSegment $ _namedBinding'name motive2) dmu1     Explicit $ Pair3
                       (Type $ Expr3 $ TermCons $ ConsUniHS $ tyEliminee1)
                       (Type $ Expr3 $ TermCons $ ConsUniHS $ tyEliminee2)
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
                        dmu1orig
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
        let segR      = Declaration (DeclNameSegment $ _namedBinding'name motive2) dmu1     Explicit $ Pair3
                          tyAmbient1
                          tyAmbient2
        let segEq1orig = Declaration (DeclNameSegment $ _namedBinding'name $ _namedBinding'body motive2)
                           (VarWkn <$> dmu1orig) Explicit
                           (Type $ Expr3 $ TermCons $ ConsUniHS $
                              EqType (VarWkn <$> tyAmbient1orig) (VarWkn <$> tL1orig) (Var3 VarLast))
        let segEq      = Declaration (DeclNameSegment $ _namedBinding'name $ _namedBinding'body motive2)
                           (VarWkn <$> dmu1    ) Explicit $
                         Pair3
                           (Type $ Expr3 $ TermCons $ ConsUniHS $
                              EqType (VarWkn <$> tyAmbient1) (VarWkn <$> tL1) (Var3 VarLast))
                           (Type $ Expr3 $ TermCons $ ConsUniHS $
                              EqType (VarWkn <$> tyAmbient2) (VarWkn <$> tL2) (Var3 VarLast))
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
        let refl :: forall w . Term mode modty w
            refl = Expr3 $ TermCons $ ConsRefl
        crefl1orig <- newRelatedMetaTerm parent deg gammaOrig gamma subst partialInv
                        crefl2
                        (substLast3 tL1 $ substLast3 refl $ _namedBinding'body $ _namedBinding'body motive1)
                        (substLast3 tL2 $ substLast3 refl $ _namedBinding'body $ _namedBinding'body motive2)
                        "Inferring refl clause."
        return $ ElimEq motive1orig crefl1orig
      (_, _) -> unreachable

------------------------------------

{-| Precondition: @partialInv . subst = Just@.
-}
solveMetaAgainstWHNF :: (MonadTC mode modty rel tc, Eq v, DeBruijnLevel v, DeBruijnLevel vOrig) =>
  Constraint mode modty rel ->
  rel v ->
  Ctx Type mode modty vOrig Void ->
  Ctx (Pair3 Type) mode modty v Void ->
  (vOrig -> v) ->
  (v -> Maybe vOrig) ->
  Term mode modty v ->
  Type mode modty v ->
  Type mode modty v ->
  [Int] ->
  [Int] ->
  tc (Term mode modty vOrig)
solveMetaAgainstWHNF parent deg gammaOrig gamma subst partialInv t2 ty1 ty2 metasTy1 metasTy2 =
  -- CMOD if deg = eqDeg and t2 does not mention any additional variables, solve fully.
  -- Otherwise, we do a weak-head solve.
  case t2 of
    Var3 v -> case partialInv v of
      Nothing -> tcBlock parent "Cannot instantiate metavariable with a variable that it does not depend on."
      Just u -> return $ Var3 u
    Expr3 t2 -> case t2 of
      TermCons c2 -> do
        c1orig <- solveMetaAgainstConstructorTerm parent deg gammaOrig gamma subst partialInv c2 ty1 ty2 metasTy1 metasTy2
        return $ Expr3 $ TermCons $ c1orig
      TermElim dmu2 eliminee2 tyEliminee2 eliminator2 -> do
        -- CMODE MODTY
        let dmu1orig = wildModedModality {-Modality by which you eliminate-}
        let dmu1 = subst <$> dmu1orig
        tyEliminee1orig <- solveMetaAgainstUniHSConstructor
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
                             (Type $ Expr3 $ TermCons $ ConsUniHS $ tyEliminee1)
                             (Type $ Expr3 $ TermCons $ ConsUniHS $ tyEliminee2)
                             "Inferring eliminee."
        let eliminee1 = subst <$> eliminee1orig
        eliminator1orig <- newRelatedEliminator parent deg gammaOrig gamma subst partialInv
                             dmu1orig
                             eliminee1orig eliminee2
                             tyEliminee1orig tyEliminee2
                             eliminator2
                             ty1 ty2
        return $ Expr3 $ TermElim dmu1orig eliminee1orig tyEliminee1orig eliminator1orig
      TermMeta _ _ -> unreachable
      TermWildcard -> unreachable
      TermQName _ _ -> unreachable
      TermSmartElim _ _ _ -> unreachable
      TermGoal _ _ -> unreachable
      TermProblem _ -> do
        tcFail parent "Nonsensical term."

{-| Precondition: @partialInv . subst = Just@.
-}
solveMetaImmediately :: (MonadTC mode modty rel tc, Eq v, DeBruijnLevel v, DeBruijnLevel vOrig) =>
  Constraint mode modty rel ->
  Ctx Type mode modty vOrig Void ->
  Ctx (Pair3 Type) mode modty v Void ->
  (vOrig -> v) ->
  (v -> Maybe vOrig) ->
  Term mode modty v ->
  Type mode modty v ->
  Type mode modty v ->
  [Int] ->
  [Int] ->
  tc (Term mode modty vOrig)
solveMetaImmediately parent gammaOrig gamma subst partialInv t2 ty1 ty2 metasTy1 metasTy2 = do
  let maybeT2orig = sequenceA $ partialInv <$> t2
  case maybeT2orig of
    Nothing -> solveMetaAgainstWHNF parent eqDeg gammaOrig gamma subst partialInv t2 ty1 ty2 metasTy1 metasTy2
    Just t2orig -> return t2orig

------------------------------------

{-| A meta is pure if it has undergone a substitution that can be inverted in the following sense:
    All variables have been substituted with variables - all different - and the inverse substitution is well-typed.

    This method returns @'Nothing'@ if the meta is pure, @'Just' (meta:metas)@ if it is presently unclear but may
    become clear if one of the listed metas is resolved, and @'Just' []@ if it is certainly false.
-}
checkMetaPure :: (MonadTC mode modty rel tc, Eq v, DeBruijnLevel v, DeBruijnLevel vOrig) =>
  Constraint mode modty rel ->
  Ctx Type mode modty vOrig Void ->
  Ctx Type mode modty v Void ->
  (vOrig -> v) ->
  Type mode modty v ->
  tc (Maybe [Int])
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
  -- If this is false, return Just []
  -- If this is true, return Nothing
  -- If this is unclear, return some metas
  return Nothing

------------------------------------

tryToSolveMeta :: (MonadTC mode modty rel tc, Eq v, DeBruijnLevel v) =>
  Constraint mode modty rel ->
  rel v ->
  Ctx (Pair3 Type) mode modty v Void ->
  Int ->
  [Term mode modty v] ->
  Term mode modty v ->
  Type mode modty v ->
  Type mode modty v ->
  [Int] ->
  [Int] ->
  tc ()
tryToSolveMeta parent deg gamma meta depcies t2 ty1 ty2 metasTy1 metasTy2 = do
  let getVar3 :: Term mode modty v -> Maybe v
      getVar3 (Var3 v) = Just v
      getVar3 _ = Nothing
  case sequenceA $ getVar3 <$> depcies of
    -- Some dependency is not a variable
    Nothing -> tcBlock parent "Cannot solve meta-variable: it has non-variable dependencies."
    -- All dependencies are variables
    Just depcyVars -> do
      let (_, repeatedVars, _) = complex depcyVars
      case repeatedVars of
        -- All variables are unique
        [] -> solveMeta parent meta ( \ gammaOrig -> do
            -- Turn list of variables into a function mapping variables from gammaOrig to variables from gamma
            let depcySubst = (depcyVars !!) . fromIntegral . (getDeBruijnLevel Proxy)
            -- Check if the meta is pure
            isPure <- checkMetaPure parent gammaOrig (fstCtx gamma) depcySubst ty1
            case isPure of
              -- If so, weak-head-solve it
              Nothing -> do
                let depcySubstInv = join . fmap (forDeBruijnLevel Proxy . fromIntegral) . flip elemIndex depcyVars
                if isEqDeg deg
                  then solveMetaImmediately parent     gammaOrig gamma depcySubst depcySubstInv t2 ty1 ty2 metasTy1 metasTy2
                  else solveMetaAgainstWHNF parent deg gammaOrig gamma depcySubst depcySubstInv t2 ty1 ty2 metasTy1 metasTy2
              -- otherwise, block and fail to solve it (we need to give a return value to solveMeta).
              Just metas -> tcBlock parent "Cannot solve meta-variable: modalities in current context are strictly weaker than in original context."
          )
        -- Some variables occur twice
        _ -> tcBlock parent "Cannot solve meta-variable: it has undergone contraction of dependencies."

tryToSolveTerm :: (MonadTC mode modty rel tc, Eq v, DeBruijnLevel v) =>
  Constraint mode modty rel ->
  rel v ->
  Ctx (Pair3 Type) mode modty v Void ->
  Term mode modty v ->
  Term mode modty v ->
  [Int] ->
  Type mode modty v ->
  Type mode modty v ->
  [Int] ->
  [Int] ->
  tc ()
tryToSolveTerm parent deg gamma tBlocked t2 metasBlocked tyBlocked ty2 metasTyBlocked metasTy2 = case tBlocked of
  -- tBlocked should be a meta
  (Expr3 (TermMeta meta depcies)) ->
    tryToSolveMeta parent deg gamma meta (getCompose depcies) t2 tyBlocked ty2 metasTyBlocked metasTy2
  -- if tBlocked is not a meta, then we should just block on its submetas
  _ -> tcBlock parent "Cannot solve relation: one side is blocked on a meta-variable."
