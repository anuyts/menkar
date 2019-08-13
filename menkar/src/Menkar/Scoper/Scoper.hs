{-# LANGUAGE FlexibleContexts, FlexibleInstances, ApplicativeDo, MultiParamTypeClasses #-}

module Menkar.Scoper.Scoper where

import Prelude hiding (pi)

import Menkar.Monad.Monad
import qualified Menkar.Raw as Raw
import qualified Menkar.PrettyPrint.Raw as Raw
import Menkar.Fine.Syntax
--import Menkar.Fine.Judgement
import Menkar.Basic.Context
--import Menkar.Scoper.Context
import Menkar.Fine.Context
import Menkar.Fine.LookupQName
import Control.Exception.AssertFalse
import Menkar.System.Fine
import Menkar.System.Scoper
import Menkar.PrettyPrint.Raw.Syntax
import Menkar.PrettyPrint.Aux.Context

import Control.Monad.State.Strict
import Control.Monad.List
import Data.Functor.Compose
import Data.Void
import Data.Functor.Identity
import Data.Functor.Coyoneda
import Data.Coerce
import Control.Lens
import Data.List
import GHC.Generics

---------------------------

{- SEARCH FOR TODOS -}

{-| @'eliminator' gamma rawElim@ scopes @rawElim@ to a fine smart eliminator. -}
eliminator :: forall sys sc v .
  (SysScoper sys, MonadScoper sys sc, DeBruijnLevel v) =>
  Ctx Type sys v ->
  Raw.Eliminator sys ->
  sc (SmartEliminator sys v)
eliminator gamma (Raw.ElimDots) = return SmartElimDots
--eliminator gamma (Raw.ElimEnd argSpec) = return $ SmartElimEnd argSpec
eliminator gamma (Raw.ElimArg argSpec rawExpr) = do
  let dgamma' = ctx'mode gamma
  dmu <- newMetaModtyNoCheck (crispCtx gamma) "Inferring modality of argument."
  fineExpr <- expr (withDom dmu :\\ gamma) rawExpr
  return $ SmartElimArg argSpec dmu fineExpr
eliminator gamma (Raw.ElimProj projSpec) = return $ SmartElimProj projSpec
eliminator gamma (Raw.ElimUnbox) = return $ SmartElimUnbox

natLiteral :: forall sys sc v .
  (SysScoper sys, MonadScoper sys sc, DeBruijnLevel v) =>
  Int -> sc (Term sys v)
natLiteral n
  | n == 0 = return $ Expr2 $ TermCons $ ConsZero
  | otherwise = Expr2 . TermCons . ConsSuc <$> natLiteral (n - 1)

qname :: forall sys sc v .
  (SysScoper sys, MonadScoper sys sc, DeBruijnLevel v) =>
  Ctx Type sys v ->
  Raw.QName ->
  sc (Term sys v)
qname gamma rawQName = case lookupQName gamma rawQName of
  Coyoneda (f :: u -> v) (maybeLdivTelescopedVal :: LookupResult sys u) ->
    case maybeLdivTelescopedVal of
      LookupResultNothing -> scopeFail $ "Not in scope: " ++ Raw.unparse rawQName
      LookupResultVar v -> return $ Var2 $ f v
      LookupResultVal ldivTelescopedVal -> return $ Expr2 $ TermQName rawQName $ Coyoneda f ldivTelescopedVal
  
{-| @'exprC' gamma rawExpr@ scopes @rawExpr@ to a term. -}
exprC :: forall sys sc v .
  (SysScoper sys, MonadScoper sys sc, DeBruijnLevel v) =>
  Ctx Type sys v ->
  Raw.ExprC sys ->
  sc (Term sys v)
exprC gamma (Raw.ExprQName rawQName) = qname gamma rawQName
exprC gamma (Raw.ExprParens rawExpr) = expr gamma rawExpr
exprC gamma (Raw.ExprNatLiteral n) = natLiteral n
exprC gamma (Raw.ExprImplicit) =
  newMetaTermNoCheck {-eqDeg-} gamma MetaBlocked Nothing "Infer explicitly omitted value."
exprC gamma (Raw.ExprGoal str) = do
  let algGoal = AlgGoal str $ Compose $ forallVarsRev Var2
  result <- newMetaTermNoCheck {-eqDeg-} gamma MetaBlocked (Just $ algGoal) "Infer goal's value."
  return $ Expr2 $ TermAlgorithm algGoal result
exprC gamma (Raw.ExprSys sysExprC) = scopeSysExprC gamma sysExprC

{-| @'elimination' gamma rawElim@ scopes @rawElim@ to a term. -}
elimination :: forall sys sc v .
  (SysScoper sys, MonadScoper sys sc, DeBruijnLevel v) =>
  Ctx Type sys v ->
  Raw.Elimination sys ->
  sc (Term sys v)
elimination gamma (Raw.Elimination rawEliminee rawElims) = do
  let dgamma' = ctx'mode gamma
  let dgamma = dgamma'
  dmus <- forM rawElims $ \_ -> newMetaModedModalityNoCheck (crispCtx gamma)
                                  "Inferring elimination modality."
  let dmuTotal : dmuTails = flip concatModedModalityDiagrammatically (uncoy dgamma) <$> tails dmus
  fineEliminee <- exprC (withDom dmuTotal :\\ gamma) rawEliminee
  --fineTy <- type4newImplicit gamma
  fineElims <- forM (zip3 dmus dmuTails rawElims) $
    \ (dmu, dmuTail, rawElim) -> (dmu :*:) <$> eliminator (withDom dmuTail :\\ gamma) rawElim
  case fineElims of
    [] -> return fineEliminee
    _  -> do
      let alg = AlgSmartElim fineEliminee (Compose fineElims)
      fineResult <- newMetaTermNoCheck {-eqDeg-} gamma MetaBlocked (Just alg) "Infer result of smart elimination."
      return . Expr2 $ TermAlgorithm alg fineResult
  --theMode <- mode4newImplicit gamma
  {-pushConstraint $ Constraint {
      constraintJudgement = JudSmartElim gamma fineEliminee fineTy fineElims fineResult,
      constraintParent = Nothing,
      constraintReason = "Scoper: Elaborate smart elimination."
    }-}
  --return fineResult

{-| @'exprB' gamma rawExpr@ scopes @rawExpr@ to a term. -}
exprB :: forall sys sc v .
  (SysScoper sys, MonadScoper sys sc, DeBruijnLevel v) =>
  Ctx Type sys v ->
  Raw.ExprB sys ->
  sc (Term sys v)
exprB gamma (Raw.ExprElimination rawElim) = elimination gamma rawElim

--------------------------------------------------

{-| @'simpleLambda' gamma rawArg rawBody@ scopes the Menkar lambda-expression @<rawArg> > <rawBody>@ to a term. -}
simpleLambda ::
  (SysScoper sys, MonadScoper sys sc, DeBruijnLevel v) =>
  Ctx Type sys v ->
  Raw.ExprB sys ->
  Raw.Expr sys ->
  sc (Term sys v)
simpleLambda gamma rawArg@(Raw.ExprElimination (Raw.Elimination boundArg [])) rawBody =
  do
    let dgamma' = ctx'mode gamma
    dmu <- newMetaModtyNoCheck (crispCtx gamma) "Infer domain mode/modality."
    fineTy <- Type <$> newMetaTermNoCheck {-eqDeg-} (withDom dmu :\\ gamma) MetaBlocked Nothing "Infer domain."
    maybeName <- case boundArg of
      Raw.ExprQName (Raw.Qualified [] name) -> return $ Just name
      Raw.ExprImplicit -> return $ Nothing
      _ -> scopeFail $
           "To the left of a '>', I expect a telescope, a single unqualified name, or an underscore: " ++ Raw.unparse rawArg
    let fineSeg = Declaration {
          _decl'name = DeclNameSegment maybeName,
          _decl'modty = withDom dmu,
          _decl'plicity = Explicit,
          _decl'opts = segOpts,
          _decl'content = fineTy
        }
    fineBody <- expr (gamma :.. (fineSeg)) rawBody
    fineCod <- Type <$> newMetaTermNoCheck (gamma :.. fineSeg) MetaBlocked Nothing "Infer codomain."
    return . Expr2 . TermCons . Lam $ Binding fineSeg $ ValRHS fineBody fineCod
simpleLambda gamma rawArg rawBody =
  scopeFail $
  "To the left of a '>', I expect a telescope, a single unqualified name, or an underscore: " ++ Raw.unparse rawArg

{-| @'buildPi' gamma fineSeg fineCod@ scopes the Menkar expression @<fineSeg> -> <fineCod>@ to a term. -}
buildPi ::
  (SysScoper sys, MonadScoper sys sc, DeBruijnLevel v) =>
  Ctx Type sys v ->
  Either (ModalityTo sys v, Term sys v) (Segment Type sys v, Term sys (VarExt v)) ->
  sc (Term sys v)
buildPi gamma (Right (fineSeg, fineCod)) = do
  --fineLvl <- term4newImplicit gamma
  --fineMode <- mode4newImplicit gamma
  return $ hs2term $ Pi $ Binding fineSeg (Type fineCod)
buildPi gamma (Left (dmu, fineCod)) = do
  return $ hs2term $ BoxType $ Declaration (DeclNameSegment Nothing) dmu Explicit segOpts (Type fineCod)

{-| @'buildSigma' gamma fineSeg fineCod@ scopes the Menkar expression @<fineSeg> >< <fineCod>@ to a term. -}
buildSigma ::
  (SysScoper sys, MonadScoper sys sc, DeBruijnLevel v) =>
  Ctx Type sys v ->
  Either (ModalityTo sys v, Term sys v) (Segment Type sys v, Term sys (VarExt v)) ->
  sc (Term sys v)
buildSigma gamma (Right (fineSeg, fineCod)) = do
  --fineLvl <- term4newImplicit gamma
  --fineMode <- mode4newImplicit gamma
  return $ Expr2 $ TermCons $ ConsUniHS $ Sigma $ Binding fineSeg (Type fineCod)
buildSigma gamma (Left (dmu, fineCod)) =
  scopeFail $ "Modal locks are not allowed in telescopes for Sigma-types."
  
{-| @'buildLambda' gamma fineSeg fineBody@ scopes the Menkar expression @<fineSeg> > <fineBody>@ to a term. -}
buildLambda ::
  (SysScoper sys, MonadScoper sys sc, DeBruijnLevel v) =>
  Ctx Type sys v ->
  Either (ModalityTo sys v, Term sys v) (Segment Type sys v, Term sys (VarExt v)) ->
  sc (Term sys v)
buildLambda gamma (Right (fineSeg, fineBody)) = do
  fineCod <- newMetaTypeNoCheck (gamma :.. fineSeg) "Infer codomain."
  return $ Expr2 $ TermCons $ Lam $ Binding fineSeg $ ValRHS fineBody fineCod
buildLambda gamma (Left (dmu, fineContent)) = do
  tyContent <- newMetaTypeNoCheck (dmu :\\ gamma) "Infer box content type."
  let boxSeg = Declaration (DeclNameSegment Nothing) dmu Explicit segOpts tyContent
  return $ Expr2 $ TermCons $ ConsBox boxSeg fineContent

{-| @'binder2' build gamma fineSegs rawArgs rawBody@ scopes the Menkar expression
    @<fineSegs> **> <rawArgs> **> rawBody@ to a term, where
    @build gamma fineSeg fineBody@ scopes the Menkar expression @<fineSeg> **> <fineBody>@ to a term. -}
binder2 ::
  (SysScoper sys, MonadScoper sys sc, DeBruijnLevel v) =>
  ( forall w .
    DeBruijnLevel w =>
    Ctx Type sys w ->
    Either (ModalityTo sys w, Term sys w) (Segment Type sys w, Term sys (VarExt w)) ->
    sc (Term sys w)
  ) ->
  Ctx Type sys v ->
  Telescoped Type Unit2 sys v ->
      {-^ remainder of the already-scoped part of the telescope on the left of the operator -}
  [Either (Raw.ModalLock sys) (Raw.Segment sys)] -> {-^ telescope on the left of the operator -}
  Raw.Expr sys -> {-^ operand on the right of the operator -}
  sc (Term sys v)
binder2 build gamma (Telescoped Unit2) rawArgs rawBody = binder build gamma rawArgs rawBody
binder2 build gamma (fineSeg :|- fineSegs) rawArgs rawBody = do
  fineCod <- binder2 build (gamma :.. (fineSeg)) fineSegs rawArgs rawBody
  build gamma $ Right (fineSeg, fineCod) 
binder2 build gamma (dmu :** fineSegs) rawArgs rawBody = do
  fineCod <- binder2 build (dmu :\\ gamma) fineSegs rawArgs rawBody
  build gamma $ Left (dmu, fineCod)

{-| @'binder' build gamma rawArgs rawBody@ scopes the Menkar expression
    @<rawArgs> **> rawBody@ to a term, where
    @build gamma fineSeg fineBody@ scopes the Menkar expression @<fineSeg> **> <fineBody>@ to a term. -}
binder ::
  (SysScoper sys, MonadScoper sys sc, DeBruijnLevel v) =>
  ( forall w .
    DeBruijnLevel w =>
    Ctx Type sys w ->
    Either (ModalityTo sys w, Term sys w) (Segment Type sys w, Term sys (VarExt w)) ->
    sc (Term sys w)
  ) ->
  Ctx Type sys v ->
  [Either (Raw.ModalLock sys) (Raw.Segment sys)] -> {-^ telescope on the left of the operator -}
  Raw.Expr sys -> {-^ operand on the right of the operator -}
  sc (Term sys v)
binder build gamma [] rawBody = expr gamma rawBody
binder build gamma (Right rawArg : rawArgs) rawBody = do
  fineArgTelescope <- segment gamma rawArg
  binder2 build gamma fineArgTelescope rawArgs rawBody
binder build gamma (Left rawLock : rawArgs) rawBody = do
  dmu <- modalLock gamma rawLock
  binder2 build gamma (dmu :** Telescoped Unit2) rawArgs rawBody

{-| @'telescopeOperation' gamma rawTheta rawOp maybeRawExprR@ scopes the Menkar expression
    @<rawTheta> <rawOp> <maybeRawExprR>@ to a term. -}
telescopeOperation ::
  (SysScoper sys, MonadScoper sys sc, DeBruijnLevel v) =>
  Ctx Type sys v ->
  Raw.Telescope sys -> {-^ telescope on the left of the operator -}
  Raw.Elimination sys -> {-^ the operator -}
  Maybe (Raw.Expr sys) -> {-^ operand on the right of the operator -}
  sc (Term sys v)
telescopeOperation gamma rawTheta
    rawOp@(Raw.Elimination _ (_ : _)) maybeRawExprR =
  scopeFail $ "Smart eliminations used on a binding operator: " ++ Raw.unparse rawOp
telescopeOperation gamma rawTheta
    rawOp@(Raw.Elimination (Raw.ExprQName (Raw.Qualified [] (Raw.Name Raw.Op opString))) []) maybeRawExprR =
  case (opString, maybeRawExprR) of
    (">", Just rawBody) -> binder buildLambda gamma (Raw.untelescope rawTheta) rawBody
    ("><", Just rawCod) -> binder buildSigma gamma (Raw.untelescope rawTheta) rawCod
    ("->", Just rawCod) -> binder buildPi gamma (Raw.untelescope rawTheta) rawCod
                           -- rawCod does not refer to an unbaked fish.
    (_, Nothing) -> scopeFail $ "Binder body/codomain is missing: " ++ Raw.unparse
      (Raw.ExprOps (Raw.OperandTelescope rawTheta) $ Just (rawOp, maybeRawExprR))
    _    -> scopeFail $ "Illegal operator name '" ++ opString ++ "': " ++ Raw.unparse
      (Raw.ExprOps (Raw.OperandTelescope rawTheta) $ Just (rawOp, maybeRawExprR))
telescopeOperation gamma theta rawOp maybeRawExprR =
  scopeFail $ "Binding operator is not an unqualified name: " ++ Raw.unparse rawOp

{-
type Fixity = Double
data Associativity = AssocLeft | AssocRight | AssocAlone
data OpTree sys v =
  OpLeaf (Term sys v) |
  OpNode {
    nodeOp :: (Term sys v),
    nodeFixity :: Fixity,
    nodeAssoc :: Associativity,
    nodeLOperand :: (OpTree sys v),
    nodeROperand :: (OpTree sys v)
    } |
  OpTelescoped {
    nodeOp :: (Term sys v),
    nodeFixity :: Fixity,
    nodeAssoc :: Associativity,
    nodeTelescope :: (OpTree sys v),
    nodeROperand :: (OpTree sys v)
    }
  deriving (Functor, Foldable, Traversable, Generic1)

exprToTree :: MonadScoper sys sc =>
  Ctx Type sys v ->
  mode v ->
  Raw.Expr ->
  sc (OpTree sys v)
exprToTree gamma _ = _exprToTree
-}

{- YOU NEED TO RESOLVE FIXITY HERE -}
{-| @'expr' gamma rawExpr@ scopes @rawExpr@ to a term.
    For now, every operator is right associative with equal precedence. -}
expr :: forall sys sc v .
  (SysScoper sys, MonadScoper sys sc, DeBruijnLevel v) =>
  Ctx Type sys v ->
  Raw.Expr sys ->
  sc (Term sys v)
-- Operator-free expression (e.g. @5@)
expr gamma (Raw.ExprOps (Raw.OperandExpr rawExpr) Nothing) = exprB gamma rawExpr
-- Simple lambda (e.g. @x > f x@)
expr gamma fullRawExpr@
             (Raw.ExprOps
               (Raw.OperandExpr boundArg)
               (Just (Raw.Elimination (Raw.ExprQName (Raw.Qualified [] (Raw.Name Raw.Op ">"))) rawElims, maybeRawBody))
             ) = case (rawElims, maybeRawBody) of
                   ([], Just rawBody) -> simpleLambda gamma boundArg rawBody
                   (_:_, _) -> scopeFail $ "Smart eliminations used on '>': " ++ Raw.unparse fullRawExpr
                   (_, Nothing) -> scopeFail $ "Body of lambda missing: " ++ Raw.unparse fullRawExpr
-- Unary operator expression (e.g. @5 ! .{arg = 3}@)
expr gamma (Raw.ExprOps (Raw.OperandExpr rawExprL) (Just (rawOp, Nothing))) = do
  elimination gamma (Raw.addEliminators rawOp [Raw.ElimArg Raw.ArgSpecExplicit (Raw.exprBtoA rawExprL)])
-- Binary operator expression (e.g. @a == .{A} b@)
expr gamma (Raw.ExprOps (Raw.OperandExpr rawExprL) (Just (rawOp, Just rawExprR))) = do
  elimination gamma (Raw.addEliminators rawOp [Raw.ElimArg Raw.ArgSpecExplicit (Raw.exprBtoA rawExprL),
                                               Raw.ElimArg Raw.ArgSpecExplicit rawExprR])
-- Naked telescope
expr gamma fullRawExpr@(Raw.ExprOps (Raw.OperandTelescope _) Nothing) =
  scopeFail $ "Naked telescope appears as expression: " ++ Raw.unparse fullRawExpr
-- Operation on telescope
expr gamma (Raw.ExprOps (Raw.OperandTelescope rawTheta) (Just (rawOp, maybeRawExprR))) =
  telescopeOperation gamma rawTheta rawOp maybeRawExprR

------------------------------------------------

{-| @'annotation' gamma rawAnnot@ scopes @rawAnnot@ to an annotation. -}
annotation :: forall sys sc v .
  (SysScoper sys, MonadScoper sys sc, DeBruijnLevel v) =>
  Ctx Type sys v ->
  Raw.Annotation sys ->
  sc (Annotation sys v)
annotation gamma (Raw.Annotation "~" Nothing) = return AnnotImplicit
annotation gamma (Raw.Annotation annotName maybeRawArg) = do
  scopeAnnotation gamma annotName maybeRawArg

type family ScopeDeclSort (rawDeclSort :: Raw.DeclSort) :: DeclSort
type instance ScopeDeclSort Raw.DeclSortVal = DeclSortVal
type instance ScopeDeclSort (Raw.DeclSortModule False) = DeclSortModule
type instance ScopeDeclSort Raw.DeclSortSegment = DeclSortSegment

{- | @'buildDeclaration' gamma generateContent partDecl@ builds a list of telescoped declarations out of @partDecl@.

     For now, arguments written between the same accolads, are required to have the same type.
     The only alternative that yields sensible error messages, is to give them different, interdependent types (as in Agda).
-}
buildDeclaration :: forall sys sc v rawDeclSort fineDeclSort content .
  (SysScoper sys, MonadScoper sys sc, DeBruijnLevel v,
   ScopeDeclSort rawDeclSort ~ fineDeclSort, Functor (Type sys)) =>
  Ctx Type sys v ->
  {-| How to generate content if absent in the partial telescoped declaration. -}
  (forall w . DeBruijnLevel w => Ctx Type sys w -> sc (content sys w)) ->
  TelescopedPartialDeclaration rawDeclSort Type content sys v ->
  sc [Declaration fineDeclSort (Telescoped Type content) sys v]
buildDeclaration gamma generateContent partDecl = do
        let dgamma' = ctx'mode gamma
            dgamma = dgamma'
        -- allocate all implicits BEFORE name fork
        mu <- case _pdecl'modty partDecl of
          Compose (Just mu') -> return mu'
          Compose Nothing -> newMetaModtyNoCheck (crispCtx gamma) "Infer modality."
        let d = case _pdecl'mode partDecl of
              Compose (Just d') -> d'
              Compose Nothing -> _modality'dom mu
        let plic = case _pdecl'plicity partDecl of
              Compose (Just plic') -> plic'
              Compose Nothing -> Explicit
        telescopedContent <- mapTelescopedDB (
            \ wkn gammadelta (Maybe2 content) -> case content of
              Compose (Just content') -> return content'
              Compose (Nothing) -> generateContent gammadelta
          ) gamma $ _pdecl'content partDecl
          {-case _pdecl'content partDecl of
          Compose (Just ty') -> return ty'
          Compose Nothing -> lift $ generateContent-}
            --type4newImplicit gammadelta {- TODO adapt this for general telescoped declarations. -}
        names <- case _pdecl'names partDecl of
          Nothing -> assertFalse $ "Nameless partial declaration!"
          Just (Raw.DeclNamesSegment maybeNames) -> return $ DeclNameSegment <$> maybeNames
          Just (Raw.DeclNamesToplevelModule qname) -> assertFalse $ "Didn't expect a toplevel module here."
          Just (Raw.DeclNamesModule string) -> return $ [DeclNameModule string]
          Just (Raw.DeclNamesVal name) -> return $ [DeclNameVal name]
            --ListT . nameHandler $ _pdecl'names partDecl
        return $ names <&> \ name -> Declaration {
          _decl'name = name,
          _decl'modty = ModalityTo d mu, --ModedModality d dgamma mu,
          _decl'plicity = plic,
          _decl'opts = _pdecl'opts partDecl,
          _decl'content = telescopedContent
          }

{-
{- | @'buildTelescopedDeclaration' gamma generateContent partTDecl@ builds a list of telescoped declarations out of @partTDecl@.

     For now, arguments written between the same accolads, are required to have the same type.
     The only alternative that yields sensible error messages, is to give them different, interdependent types (as in Agda).
-}
buildTelescopedDeclaration :: (MonadScoper sys sc, ScopeDeclSort rawDeclSort ~ fineDeclSort) =>
  Ctx Type sys v Void ->
  {-| How to generate content if absent in the partial telescoped declaration. -}
  (forall w . Ctx Type sys w Void -> sc (content sys w)) ->
  TelescopedPartialDeclaration rawDeclSort Type content sys v ->
  sc [TelescopedDeclaration fineDeclSort Type content sys v]
buildTelescopedDeclaration gamma generateContent partTDecl = runListT $ mapTelescopedDBSc (
    \ wkn gammadelta partDecl -> ListT $ buildDeclaration gammadelta (generateContent gammadelta) partDecl
  ) gamma partTDecl
-}

{- | @'buildSegment' gamma partSeg@ builds a list of segments out of @partSeg@.

     For now, arguments written between the same accolads, are required to have the same type.
     The only alternative that yields sensible error messages, is to give them different, interdependent types (as in Agda).
-}
buildSegment :: forall sys sc v .
  (SysScoper sys, MonadScoper sys sc, DeBruijnLevel v) =>
  Ctx Type sys v ->
  PartialSegment Type sys v -> -- ~ TelescopedPartialDeclaration Raw.DeclSortSegment Type Type sys v
  sc [Segment Type sys v]
buildSegment gamma partSeg = do
  teleSegs :: [Segment (Telescoped Type Type) sys v]
              -- ~ [Declaration DeclSortSegment (Telescoped Type Type) sys v]
           <- let gen gamma = Type <$> newMetaTermNoCheck {-eqDeg-} gamma MetaBlocked Nothing "Infer type."
              in  buildDeclaration gamma gen partSeg
  return $ teleSegs <&> decl'content %~ \ case
    Telescoped seg -> seg
    (seg' :|- seg) -> unreachable
    (mu :** seg) -> unreachable
    
{-| @'partialTelescopedDeclaration' gamma rawDecl@ scopes @rawDecl@ (possibly a segment)
    to a partial telescoped declaration. -}
partialTelescopedDeclaration :: forall sys sc v rawDeclSort .
  (SysScoper sys, MonadScoper sys sc, DeBruijnLevel v) =>
  Ctx Type sys v ->
  Raw.Declaration sys rawDeclSort ->
  DeclOptions ->
  sc (TelescopedPartialDeclaration rawDeclSort Type Type sys v)
partialTelescopedDeclaration gamma rawDecl fineOpts = (flip execStateT $ newPartialDeclaration fineOpts) $ do
  --telescope
  fineDelta <- telescope gamma $ Raw.decl'telescope rawDecl
  --names
  pdecl'names .= (Just $ Raw.decl'names rawDecl)
  --type
  fineContent <- mapTelescopedDB (
      \wkn gammadelta Unit2 -> case Raw.decl'content rawDecl of
        Raw.DeclContentEmpty -> return $ Maybe2 $ Compose $ Nothing
        Raw.DeclContent rawTy -> Maybe2 . Compose . Just <$> do
          --fineLvl <- term4newImplicit gammadelta
          Type <$> expr gammadelta rawTy
    ) gamma fineDelta
  pdecl'content .= fineContent
  --annotations
  fineAnnots <- sequenceA $ annotation gamma <$> Raw.decl'annotations rawDecl
  forM_ fineAnnots $
            \ fineAnnot ->
              case fineAnnot of
                AnnotMode fineMode -> do
                  -- _Wrapped' is a lens for Compose
                  maybeOldFineMode <- use $ pdecl'mode._Wrapped'
                  case maybeOldFineMode of
                    Just oldFineMode -> scopeFail $ "Encountered multiple mode annotations: " ++ Raw.unparse rawDecl
                    Nothing -> pdecl'mode._Wrapped' .= Just fineMode
                AnnotModality fineModty -> do
                  maybeOldFineModty <- use $ pdecl'modty._Wrapped'
                  case maybeOldFineModty of
                    Just oldFineModty -> scopeFail $ "Encountered multiple modality annotations: " ++ Raw.unparse rawDecl
                    Nothing -> pdecl'modty._Wrapped' .= Just fineModty
                AnnotImplicit -> do
                  maybeOldFinePlicity <- use $ pdecl'plicity._Wrapped'
                  case maybeOldFinePlicity of
                    Just oldFinePlicity -> scopeFail $ "Encountered multiple visibility annotations: " ++ Raw.unparse rawDecl
                    Nothing -> pdecl'plicity._Wrapped' .= Just Implicit
  return ()

{-| @'partialSegment' gamma rawSeg@ scopes @rawSeg@ to a partial segment. -}
partialSegment :: forall sys sc v .
  (SysScoper sys, MonadScoper sys sc, DeBruijnLevel v) =>
  Ctx Type sys v ->
  Raw.Declaration sys Raw.DeclSortSegment ->
  --sc [Segment Type sys v]
  sc (PartialSegment Type sys v)
partialSegment gamma rawSeg = do
  telescopedPartSeg :: PartialSegment Type sys v
    <- partialTelescopedDeclaration gamma rawSeg segOpts
  case _pdecl'content telescopedPartSeg of
    Telescoped (Maybe2 ty) -> return telescopedPartSeg
      --old code, but it does nothing:
      --flip pdecl'content telescopedPartSeg $ \_ -> return $ Telescoped $ Maybe2 ty
    _ -> unreachable -- nested segments encountered

{-
  case telescopedPartSeg of
    Telescoped partSeg -> return partSeg
    _ -> unreachable -- nested segments encountered
-}

{-| Chain a list of fine segments to a fine telescope; while avoiding shadowing. -}
segments2telescoped :: forall sys sc v .
  (SysScoper sys, MonadScoper sys sc, SysTrav sys) =>
  Ctx Type sys v ->
  [Segment Type sys v] ->
  sc (Telescoped Type Unit2 sys v)
segments2telescoped gamma [] =
  return $ Telescoped Unit2
segments2telescoped gamma (fineSeg:fineSegs) = do
  -- Prevent shadowing:
  let DeclNameSegment maybeNewName = _decl'name fineSeg
  case maybeNewName of
    Nothing -> return ()
    Just newName -> case lookupQName gamma (Raw.Qualified [] newName) of
      Coyoneda _ LookupResultNothing -> return ()
      _ -> scopeFail $ "Shadowing is not allowed in variable names; already in scope: " ++ Raw.unparse newName
  -- Actual action:
  (fineSeg :|-) <$> segments2telescoped (gamma :.. (fineSeg)) (fmap VarWkn <$> fineSegs)

modalLock ::
  (SysScoper sys, MonadScoper sys sc, DeBruijnLevel v) =>
  Ctx Type sys v ->
  Raw.ModalLock sys ->
  sc (ModalityTo sys v)
modalLock gamma (Raw.ModalLock rawAnnots) = do
  let dgamma' = ctx'mode gamma
      dgamma = dgamma'
  fineAnnots <- sequenceA $ annotation gamma <$> rawAnnots
  (maybeDom, maybeMu) <- flip execStateT (Nothing, Nothing) $ forM_ fineAnnots $ \ case
    AnnotMode fineMode -> use _1 >>= \ case
      Just _ -> scopeFail $ "Encountered multiple mode annotations."
      Nothing -> _1 .= Just fineMode
    AnnotModality fineModty -> use _2 >>= \ case
      Just _ -> scopeFail $ "Encountered multiple modality annotations."
      Nothing -> _2 .= Just fineModty
    AnnotImplicit -> scopeFail $ "Encountered plicity annotation in a modal lock."
  {-dom <- case maybeDom of
    Nothing -> newMetaModeNoCheck (crispModalityTo dgamma' :\\ gamma) "Inferring domain of modality."
    Just dom -> return dom-}
  mu <- case maybeMu of
    Nothing -> newMetaModtyNoCheck (crispCtx gamma) "Inferring modality."
    Just mu -> return mu
  let dom = case maybeDom of
        Nothing -> _modality'dom mu
        Just dom -> dom
  return $ ModalityTo dom mu

segment ::
  (SysScoper sys, MonadScoper sys sc, DeBruijnLevel v) =>
  Ctx Type sys v ->
  Raw.Segment sys ->
  sc (Telescoped Type Unit2 sys v)
segment gamma (Raw.Segment rawDecl) = do
  partialSeg <- partialSegment gamma rawDecl
  segments2telescoped gamma =<< buildSegment gamma partialSeg

{-| scope a partly fine, partly raw telescope to a fine telescope. -}
telescope2 :: forall sys sc v .
  (SysScoper sys, MonadScoper sys sc, DeBruijnLevel v) =>
  Ctx Type sys v ->
  Telescoped Type Unit2 sys v ->
  Raw.Telescope sys ->
  sc (Telescoped Type Unit2 sys v)
telescope2 gamma (Telescoped Unit2) rawTele = telescope gamma rawTele
telescope2 gamma (fineSeg :|- fineSegs) rawTele =
  (fineSeg :|-) <$> telescope2 (gamma :.. (fineSeg)) fineSegs rawTele
telescope2 gamma (dmu :** fineSegs) rawTele =
  (dmu :**) <$> telescope2 (dmu :\\ gamma) fineSegs rawTele

telescope :: forall sys sc v .
  (SysScoper sys, MonadScoper sys sc, DeBruijnLevel v) =>
  Ctx Type sys v ->
  Raw.Telescope sys ->
  sc (Telescoped Type Unit2 sys v)
telescope gamma (Raw.Telescope []) = return $ Telescoped Unit2
telescope gamma (Raw.Telescope (Right rawSeg : rawSegs)) = do
  fineFrontSegs <- segment gamma rawSeg
  telescope2 gamma fineFrontSegs (Raw.Telescope rawSegs)
telescope gamma (Raw.Telescope (Left rawLock : rawSegs)) = do
  dmu <- modalLock gamma rawLock
  telescope2 gamma (dmu :** Telescoped Unit2) (Raw.Telescope rawSegs)

----------------------------------------------------------

{-| Scope a raw LHS and a raw value RHS to a value, or fail. -}
val :: forall sys sc v .
  (SysScoper sys, MonadScoper sys sc, DeBruijnLevel v) =>
  Ctx Type sys v ->
  Raw.Declaration sys Raw.DeclSortVal ->
  Raw.RHS sys Raw.DeclSortVal ->
  sc (Val sys v)
val gamma rawLHS (Raw.RHSVal rawExpr) = do
  partialLHS :: TelescopedPartialDeclaration Raw.DeclSortVal Type Type sys v
    <- partialTelescopedDeclaration gamma rawLHS entryOpts
  [fineLHS] :: [Declaration DeclSortVal (Telescoped Type Type) sys v]
            <- let gen gamma = Type <$> newMetaTermNoCheck {-eqDeg-} gamma MetaBlocked Nothing "Infer type."
               in  buildDeclaration gamma gen partialLHS
  val :: Val sys v -- ~ Declaration DeclSortVal (Telescoped Type ValRHS) sys v
    <- flip decl'content fineLHS $ mapTelescopedDB (
      \wkn gammadelta fineTy -> do
        fineTm <- expr gammadelta rawExpr
        return $ ValRHS fineTm fineTy
    ) gamma
  case lookupQName gamma (Raw.Qualified [] $ _val'name val) of
    Coyoneda _ LookupResultNothing -> return val
    _ -> scopeFail $ "Shadowing is not allowed in value names; already in scope: " ++ Raw.unparse (_val'name val)

{-| @'entryInModule' gamma fineModule rawEntry@ scopes the entry @rawEntry@ as part of the module @fineModule@ -}
entryInModule :: forall sys sc v .
  (SysScoper sys, MonadScoper sys sc, DeBruijnLevel v) =>
  Ctx Type sys v ->
  Raw.AnyEntry sys ->
  ModuleRHS sys v ->
  sc (ModuleRHS sys v)
entryInModule gamma rawEntry fineModule = do
  let gammaModule = gamma :<...> fineModule
        {-(Left <$> ModuleInScope {
          moduleContramod = ModedContramodality d _confused,
          moduleContents = modul
        })-}
  fineEntry <- anyEntry gammaModule rawEntry
  return $ addToModule fineEntry fineModule

{-| @'entriesInModule' gamma fineModule rawEntry@ scopes @rawEntries@ as part of the module @fineModule@ -}
entriesInModule :: forall sys sc v .
  (SysScoper sys, MonadScoper sys sc, DeBruijnLevel v) =>
  Ctx Type sys v ->
  [Raw.AnyEntry sys] ->
  ModuleRHS sys v ->
  sc (ModuleRHS sys v)
entriesInModule gamma rawEntries fineModule = foldl (>>=) (return fineModule) (entryInModule gamma <$> rawEntries)
{- entriesInModule gamma [rawEntry1, rawEntry2] fineModule
   = fold (>>=) (return fineModule) [\fineModule' -> entryInModule gamma rawEntry1 fineModule',
                                     \fineModule' -> entryInModule gamma rawEntry2 fineModule']
   = do
       fm1 <- return fineModule
       fm2 <- entryInModule gamma rawEntry1 fm1
       entryInModule gamma rawEntry2 fm2
-}

{-| @'modul' gamma rawLHS rawRHS@ scopes the module @<rawLHS> <rawRHS>@ (not the top-level module). -}
modul :: forall sys sc v .
  (SysScoper sys, MonadScoper sys sc, DeBruijnLevel v) =>
  Ctx Type sys v ->
  Raw.Declaration sys (Raw.DeclSortModule False) ->
  Raw.RHS sys (Raw.DeclSortModule False) ->
  sc (Module sys v)
modul gamma rawLHS rawRHS@(Raw.RHSModule rawEntries) = do
  partialLHS :: TelescopedPartialDeclaration (Raw.DeclSortModule False) Type Type sys v
    <- partialTelescopedDeclaration gamma rawLHS entryOpts
  partialLHSUntyped :: TelescopedPartialDeclaration (Raw.DeclSortModule False) Type Unit2 sys v
    <- flip pdecl'content partialLHS $ mapTelescopedDB (
      \wkn gammadelta (Maybe2 maybeFineTy) -> case maybeFineTy of
        Compose Nothing -> return $ Maybe2 $ Compose Nothing
        Compose (Just fineTy) -> scopeFail $ "Modules do not have a type: " ++ Raw.unparse rawLHS
    ) gamma
  [fineLHS] :: [Declaration DeclSortModule (Telescoped Type Unit2) sys v]
    <- buildDeclaration gamma (\gammadelta -> return Unit2) partialLHSUntyped
  flip decl'content fineLHS $ mapTelescopedDB (
      \wkn gammadelta Unit2 -> entriesInModule gammadelta rawEntries newModule
    ) gamma
--modul gamma rawLHS rawRHS = scopeFail $ "Not a valid RHS for a 'val': " ++ Raw.unparse rawRHS

entry :: forall sys sc v rawDeclSort .
  (SysScoper sys, MonadScoper sys sc, DeBruijnLevel v) =>
  Ctx Type sys v ->
  Raw.Entry sys rawDeclSort ->
  sc (Entry sys v)
entry gamma (Raw.EntryLR Raw.HeaderVal rawLHS rawRHS) = EntryVal <$> val gamma rawLHS rawRHS
entry gamma (Raw.EntryLR Raw.HeaderModule rawLHS rawRHS) = EntryModule <$> modul gamma rawLHS rawRHS
entry gamma rawEntry = scopeFail $ "Nonsensical or unsupported entry: " ++ Raw.unparse rawEntry

anyEntry :: forall sys sc v .
  (SysScoper sys, MonadScoper sys sc, DeBruijnLevel v) =>
  Ctx Type sys v ->
  Raw.AnyEntry sys ->
  sc (Entry sys v)
anyEntry gamma (Raw.AnyEntry rawEntry) = entry gamma rawEntry

file :: forall sys sc v .
  (SysScoper sys, MonadScoper sys sc, DeBruijnLevel v) =>
  Ctx Type sys v ->
  Raw.File sys ->
  sc (Entry sys v)
file gamma rawFile = entry gamma (Raw.file2nestedModules rawFile)

{-| Takes a bunch of raw entries and scopes them in a new module called @"Root"@.
-}
bulk :: forall sys sc v .
  (SysScoper sys, MonadScoper sys sc, DeBruijnLevel v) =>
  Ctx Type sys v ->
  [Raw.AnyEntry sys] ->
  sc (Entry sys v)
bulk gamma rawEntries = do
    let rawModuleLHS = Raw.Declaration
          rawRootAnnots
          (Raw.DeclNamesModule "Root")
          (Raw.Telescope [])
          Raw.DeclContentEmpty -- modules have no type
    let rawModuleRHS = Raw.RHSModule $ rawEntries
    let rawModule = Raw.EntryLR Raw.HeaderModule rawModuleLHS rawModuleRHS
    entry gamma rawModule
  
