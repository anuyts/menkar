{-# LANGUAGE FlexibleContexts, FlexibleInstances, ApplicativeDo, MultiParamTypeClasses #-}

module Menkar.Scoper where

import Prelude hiding (pi)
import Menkar.TCMonad.MonadScoper
import qualified Menkar.Raw as Raw
import Menkar.Fine.Syntax
import Menkar.Fine.Judgement
import Menkar.Fine.Substitution
import Menkar.Fine.Context.Variable
import Menkar.Fine.Context
import Control.Exception.AssertFalse
import Control.Monad.State.Lazy
import Control.Monad.List
import Data.Functor.Compose
import Data.Void
import Data.HashMap.Lazy
import Data.Functor.Identity
import Data.Coerce

{- SEARCH FOR TODOS -}

{-| @'eliminator' gamma d rawElim@ scopes @rawElim@ to a fine smart eliminator. -}
eliminator :: MonadScoper mode modty rel sc =>
  Ctx Type mode modty v Void ->
  mode v ->
  Raw.Eliminator ->
  sc (SmartEliminator mode modty v)
eliminator gamma d (Raw.ElimEnd argSpec) = return $ SmartElimEnd argSpec
eliminator gamma d (Raw.ElimArg argSpec rawExpr) = do
  fineExpr <- expr gamma d rawExpr
  return $ SmartElimArg argSpec fineExpr
eliminator gamma d (Raw.ElimProj projSpec) = return $ SmartElimProj projSpec

{-| @'expr3' gamma d rawExpr@ scopes @rawExpr@ to a term. -}
expr3 :: MonadScoper mode modty rel sc =>
  Ctx Type mode modty v Void ->
  mode v ->
  Raw.Expr3 ->
  sc (Term mode modty v)
expr3 gamma d (Raw.ExprQName rawQName) = term4val gamma d rawQName
expr3 gamma d (Raw.ExprParens rawExpr) = expr gamma d rawExpr
expr3 gamma d (Raw.ExprNatLiteral n) = todo
expr3 gamma d (Raw.ExprImplicit) = term4newImplicit gamma d

{-| @'elimination' gamma d rawElim@ scopes @rawElim@ to a term. -}
elimination :: MonadScoper mode modty rel sc =>
  Ctx Type mode modty v Void ->
  mode v ->
  Raw.Elimination ->
  sc (Term mode modty v)
elimination gamma d (Raw.Elimination rawExpr rawElims) = do
  fineExpr <- expr3 gamma d rawExpr
  fineTy <- type4newImplicit gamma d
  fineElims <- sequenceA (eliminator gamma d <$> rawElims)
  fineResult <- term4newImplicit gamma d
  --theMode <- mode4newImplicit gamma
  pushConstraint $ Constraint {
      constraintJudgement = JudSmartElim gamma d fineExpr fineTy fineElims fineResult,
      constraintParent = Nothing,
      constraintReason = "Scoper: Elaborate smart elimination."
    }
  return fineResult

{-| @'expr2' gamma d rawExpr@ scopes @rawExpr@ to a term. -}
expr2 :: MonadScoper mode modty rel sc =>
  Ctx Type mode modty v Void ->
  mode v ->
  Raw.Expr2 ->
  sc (Term mode modty v)
expr2 gamma d (Raw.ExprElimination rawElim) = elimination gamma d rawElim

--------------------------------------------------

{-| @'simpleLambda' gamma d rawArg rawBody@ scopes the Menkar lambda-expression @<rawArg> > <rawBody>@ to a term. -}
simpleLambda :: MonadScoper mode modty rel sc =>
  Ctx Type mode modty v Void ->
  mode v ->
  Raw.Expr2 ->
  Raw.Expr ->
  sc (Term mode modty v)
simpleLambda gamma d rawArg@(Raw.ExprElimination (Raw.Elimination boundArg [])) rawBody =
  do
    d <- mode4newImplicit gamma d
    mu <- modty4newImplicit gamma d
    fineTy <- type4newImplicit gamma d
    maybeName <- case boundArg of
      Raw.ExprQName (Raw.Qualified [] name) -> return $ Just name
      Raw.ExprImplicit -> return $ Nothing
      _ -> scopeFail $
           "To the left of a '>', I expect a telescope, a single unqualified name, or an underscore: " ++ Raw.unparse rawArg
    let fineSeg = Segment {
          segmentName = maybeName,
          segmentModality = ModedModality d mu,
          segmentVisibility = Visible,
          segmentRHS = Telescoped fineTy,
          segmentRightCartesian = False
       }
    fineBody <- expr (gamma :.. (VarFromCtx <$> fineSeg)) (VarWkn <$> d) rawBody
    return . Expr . TermCons . Lam $ Binding fineSeg fineBody
simpleLambda gamma d rawArg rawBody =
  scopeFail $
  "To the left of a '>', I expect a telescope, a single unqualified name, or an underscore: " ++ Raw.unparse rawArg

{-| @'buildPi' gamma d fineSeg fineCod@ scopes the Menkar expression @<fineSeg> -> <fineCod>@ to a term. -}
buildPi :: MonadScoper mode modty rel sc =>
  Ctx Type mode modty v Void ->
  mode v ->
  Segment Type Type mode modty v ->
  Term mode modty (VarExt v) ->
  sc (Term mode modty v)
buildPi gamma d fineSeg fineCod = do
  fineLvl <- term4newImplicit gamma d
  return $ Expr $ TermCons $ ConsUnsafeResize d fineLvl fineLvl $ Pi $ Binding fineSeg fineCod

{-| @'buildSigma' gamma d fineSeg fineCod@ scopes the Menkar expression @<fineSeg> >< <fineCod>@ to a term. -}
buildSigma :: MonadScoper mode modty rel sc =>
  Ctx Type mode modty v Void ->
  mode v ->
  Segment Type Type mode modty v ->
  Term mode modty (VarExt v) ->
  sc (Term mode modty v)
buildSigma gamma d fineSeg fineCod = do
  fineLvl <- term4newImplicit gamma d
  return $ Expr $ TermCons $ ConsUnsafeResize d fineLvl fineLvl $ Sigma $ Binding fineSeg fineCod
  
{-| @'buildLambda' gamma d fineSeg fineBody@ scopes the Menkar expression @<fineSeg> > <fineBody>@ to a term. -}
buildLambda :: MonadScoper mode modty rel sc =>
  Ctx Type mode modty v Void ->
  mode v ->
  Segment Type Type mode modty v ->
  Term mode modty (VarExt v) ->
  sc (Term mode modty v)
buildLambda gamma d fineSeg fineCod =
  return $ Expr $ TermCons $ Lam $ Binding fineSeg fineCod

{-| @'binder2' build gamma d fineSegs rawArgs rawBody@ scopes the Menkar expression
    @<fineSegs> **> <rawArgs> **> rawBody@ to a term, where
    @build gamma d fineSeg fineBody@ scopes the Menkar expression @<fineSeg> **> <fineBody>@ to a term. -}
binder2 :: MonadScoper mode modty rel sc =>
  ( forall w .
    Ctx Type mode modty w Void ->
    mode w ->
    Segment Type Type mode modty w ->
    Term mode modty (VarExt w) ->
    sc (Term mode modty w)
  ) ->
  Ctx Type mode modty v Void ->
  mode v ->
  Telescoped Type Unit3 mode modty v ->
      {-^ remainder of the already-scoped part of the telescope on the left of the operator -}
  [Raw.Segment] -> {-^ telescope on the left of the operator -}
  Raw.Expr -> {-^ operand on the right of the operator -}
  sc (Term mode modty v)
binder2 build gamma d (Telescoped Unit3) rawArgs rawBody = binder build gamma d rawArgs rawBody
binder2 build gamma d (fineSeg :|- fineSegs) rawArgs rawBody =
  build gamma d fineSeg =<< binder2 build (gamma :.. (VarFromCtx <$> fineSeg)) (VarWkn <$> d) fineSegs rawArgs rawBody

{-| @'binder' build gamma d rawArgs rawBody@ scopes the Menkar expression
    @<rawArgs> **> rawBody@ to a term, where
    @build gamma d fineSeg fineBody@ scopes the Menkar expression @<fineSeg> **> <fineBody>@ to a term. -}
binder :: MonadScoper mode modty rel sc =>
  ( forall w .
    Ctx Type mode modty w Void ->
    mode w ->
    Segment Type Type mode modty w ->
    Term mode modty (VarExt w) ->
    sc (Term mode modty w)
  ) ->
  Ctx Type mode modty v Void ->
  mode v ->
  [Raw.Segment] -> {-^ telescope on the left of the operator -}
  Raw.Expr -> {-^ operand on the right of the operator -}
  sc (Term mode modty v)
binder build gamma d [] rawBody = expr gamma d rawBody
binder build gamma d (rawArg:rawArgs) rawBody = do
  fineArgTelescoped <- segment gamma d rawArg
  binder2 build gamma d fineArgTelescoped rawArgs rawBody

{-| @'telescopeOperation' gamma d rawTheta rawOp maybeRawExprR@ scopes the Menkar expression
    @<rawTheta> <rawOp> <maybeRawExprR>@ to a term. -}
telescopeOperation :: MonadScoper mode modty rel sc =>
  Ctx Type mode modty v Void ->
  mode v ->
  Raw.Telescope -> {-^ telescope on the left of the operator -}
  Raw.Elimination -> {-^ the operator -}
  Maybe (Raw.Expr) -> {-^ operand on the right of the operator -}
  sc (Term mode modty v)
telescopeOperation gamma d rawTheta
    rawOp@(Raw.Elimination _ (_ : _)) maybeRawExprR =
  scopeFail $ "Smart eliminations used on a binding operator: " ++ Raw.unparse rawOp
telescopeOperation gamma d rawTheta
    rawOp@(Raw.Elimination (Raw.ExprQName (Raw.Qualified [] (Raw.Name Raw.Op opString))) []) maybeRawExprR =
  case (opString, maybeRawExprR) of
    (">", Just rawBody) -> binder buildLambda gamma d (Raw.untelescope rawTheta) rawBody
    ("><", Just rawCod) -> binder buildSigma gamma d (Raw.untelescope rawTheta) rawCod
    ("->", Just rawCod) -> binder buildPi gamma d (Raw.untelescope rawTheta) rawCod
                           -- rawCod does not refer to an unbaked fish.
    (_, Nothing) -> scopeFail $ "Binder body/codomain is missing."
    _    -> scopeFail $ "Illegal operator name: " ++ opString
telescopeOperation gamma d theta rawOp maybeRawExprR =
  scopeFail $ "Binding operator is not an unqualified name: " ++ Raw.unparse rawOp

{-
type Fixity = Double
data Associativity = AssocLeft | AssocRight | AssocAlone
data OpTree mode modty v =
  OpLeaf (Term mode modty v) |
  OpNode {
    nodeOp :: (Term mode modty v),
    nodeFixity :: Fixity,
    nodeAssoc :: Associativity,
    nodeLOperand :: (OpTree mode modty v),
    nodeROperand :: (OpTree mode modty v)
    } |
  OpTelescoped {
    nodeOp :: (Term mode modty v),
    nodeFixity :: Fixity,
    nodeAssoc :: Associativity,
    nodeTelescope :: (OpTree mode modty v),
    nodeROperand :: (OpTree mode modty v)
    }
  deriving (Functor, Foldable, Traversable, Generic1)

exprToTree :: MonadScoper mode modty rel sc =>
  Ctx Type mode modty v ->
  mode v ->
  Raw.Expr ->
  sc (OpTree mode modty v)
exprToTree gamma d _ = _exprToTree
-}

{- YOU NEED TO RESOLVE FIXITY HERE -}
{-| @'expr' gamma d rawExpr@ scopes @rawExpr@ to a term.
    For now, every operator is right associative with equal precedence. -}
expr :: MonadScoper mode modty rel sc =>
  Ctx Type mode modty v Void ->
  mode v ->
  Raw.Expr ->
  sc (Term mode modty v)
-- Operator-free expression (e.g. @5@)
expr gamma d (Raw.ExprOps (Raw.OperandExpr rawExpr) Nothing) = expr2 gamma d rawExpr
-- Simple lambda (e.g. @x > f x@)
expr gamma d fullRawExpr@
             (Raw.ExprOps
               (Raw.OperandExpr boundArg)
               (Just (Raw.Elimination (Raw.ExprQName (Raw.Qualified [] (Raw.Name Raw.Op ">"))) rawElims, maybeRawBody))
             ) = case (rawElims, maybeRawBody) of
                   ([], Just rawBody) -> simpleLambda gamma d boundArg rawBody
                   (_:_, _) -> scopeFail $ "Smart eliminations used on '>': " ++ Raw.unparse fullRawExpr
                   (_, Nothing) -> scopeFail $ "Body of lambda missing: " ++ Raw.unparse fullRawExpr
-- Unary operator expression (e.g. @5 ! .{arg = 3}@)
expr gamma d (Raw.ExprOps (Raw.OperandExpr rawExprL) (Just (rawOp, Nothing))) = do
  elimination gamma d (Raw.addEliminators rawOp [Raw.ElimArg Raw.ArgSpecVisible (Raw.expr2to1 rawExprL)])
-- Binary operator expression (e.g. @a == .{A} b@)
expr gamma d (Raw.ExprOps (Raw.OperandExpr rawExprL) (Just (rawOp, Just rawExprR))) = do
  elimination gamma d (Raw.addEliminators rawOp [Raw.ElimArg Raw.ArgSpecVisible (Raw.expr2to1 rawExprL),
                                              Raw.ElimArg Raw.ArgSpecVisible rawExprR])
-- Naked telescope
expr gamma d fullRawExpr@(Raw.ExprOps (Raw.OperandTelescope _) Nothing) =
  scopeFail $ "Naked telescope appears as expression: " ++ Raw.unparse fullRawExpr
-- Operation on telescope
expr gamma d (Raw.ExprOps (Raw.OperandTelescope rawTheta) (Just (rawOp, maybeRawExprR))) =
  telescopeOperation gamma d rawTheta rawOp maybeRawExprR

------------------------------------------------

{-| @'annotation' gamma d rawAnnot@ scopes @rawAnnot@ to an annotation. -}
annotation :: MonadScoper mode modty rel sc =>
  Ctx Type mode modty v Void ->
  mode v ->
  Raw.Annotation ->
  sc (Annotation mode modty v)
annotation gamma d (Raw.Annotation (Raw.Qualified [] "~") []) = return AnnotImplicit
annotation gamma d (Raw.Annotation qstring rawExprs) = do
  fineExprs <- sequenceA $ expr3 gamma d <$> rawExprs
  annot4annot gamma d qstring fineExprs

{-| @'mapTelescoped' f gamma <theta |- rhs>@ yields @<theta |- f wkn (gamma.theta) rhs>@ -}
mapTelescoped :: (Functor h, Functor mode, Functor modty, Functor (ty mode modty)) =>
  (forall w . (v -> w) -> Ctx ty mode modty w Void -> rhs1 mode modty w -> h (rhs2 mode modty w)) ->
  (Ctx ty mode modty v Void -> Telescoped ty rhs1 mode modty v -> h (Telescoped ty rhs2 mode modty v))
mapTelescoped f gamma (Telescoped rhs) = Telescoped <$> f id gamma rhs
mapTelescoped f gamma (seg :|- stuff) = (seg :|-) <$> mapTelescoped (f . (. VarWkn)) (gamma :.. (VarFromCtx <$> seg)) stuff

{-| @'segmentNamesHandler' gamma d@ fails or maps @'SomeNamesForTelescope' rawNames@ to @rawNames@ -}
segmentNamesHandler :: MonadScoper mode modty rel sc =>
  Ctx Type mode modty v Void ->
  mode v ->
  Raw.LHSNames ->
  sc [Maybe Raw.Name]
segmentNamesHandler gamma d rawLHSNames = case rawLHSNames of
    Raw.SomeNamesForTelescope rawNames -> return rawNames
    Raw.QNameForEntry rawQName ->
      assertFalse $ "I thought I was scoping a telescope segment, but it was parsed as an entry: " ++ Raw.unparse rawQName
    Raw.NoNameForConstraint -> assertFalse "Constraints are abolished."

{-| @'nestedEntryNamesHandler' gamma d@ fails or maps @'QNameForEntry' (Qualified [] rawName)@ to @[rawName]@ -}
nestedEntryNamesHandler :: MonadScoper mode modty rel sc =>
  Ctx Type mode modty v Void ->
  mode v ->
  Raw.LHSNames ->
  sc [Maybe Raw.Name]
nestedEntryNamesHandler gamma d rawLHSNames = case rawLHSNames of
    (Raw.SomeNamesForTelescope rawNames) -> 
      assertFalse $ "I thought I was scoping an entry, but it was parsed as a telescope segment: " ++ Raw.unparse rawLHSNames
    Raw.QNameForEntry (Raw.Qualified [] rawName) -> return $ [Just rawName]
    Raw.QNameForEntry rawQName ->
      scopeFail $ "Not supposed to be qualified: " ++ Raw.unparse rawQName
    Raw.NoNameForConstraint -> assertFalse "Constraints are abolished."

{- | @'buildSegment' gamma d segBuilder nameHandler@ builds a list of segments out of @segBuilder@.

     For now, arguments written between the same accolads, are required to have the same type.
     The only alternative that yields sensible error messages, is to give them different, interdependent types (as in Agda).
-}
buildSegment :: MonadScoper mode modty rel sc =>
  Ctx Type mode modty v Void ->
  mode v ->
  SegmentBuilder Type Type mode modty v ->
  (Raw.LHSNames -> sc [Maybe Raw.Name]) ->
  sc [Segment Type Type mode modty v]
buildSegment gamma d segBuilder nameHandler = runListT $ do
  -- allocate all implicits BEFORE name fork
  d <- case segmentBuilderMode segBuilder of
    Compose (Just d') -> return d'
    Compose Nothing -> mode4newImplicit gamma d
  mu <- case segmentBuilderModality segBuilder of
    Compose (Just mu') -> return mu'
    Compose Nothing -> modty4newImplicit gamma d
  let vis = case segmentBuilderVisibility segBuilder of
        Compose (Just vis') -> vis'
        Compose Nothing -> Visible
  rhs <- mapTelescoped (
           \ wkn gammadelta (Maybe3 (Compose maybeTy)) -> case maybeTy of
               Just ty -> return ty
               Nothing -> type4newImplicit gammadelta (wkn <$> d)
         ) gamma (segmentBuilderTelescopedType segBuilder)
  -- fork
  name <- ListT . nameHandler $ segmentBuilderNames segBuilder
    {-case segmentBuilderNames builder of
    Raw.SomeNamesForTelescope names -> return names
    Raw.QNameForEntry qname ->
      scopeFail $ "I thought I was scoping a telescope segment, but it was parsed as an entry: " ++ Raw.unparse qname
    Raw.NoNameForConstraint -> assertFalse "Constraints are abolished."-}
  return Segment {
      segmentName = name,
      segmentModality = ModedModality d mu,
      segmentVisibility = vis,
      segmentRHS = rhs,
      segmentRightCartesian = False
    }

{- THERE IS A FUNDAMENTAL PROBLEM HERE:
   -The mode & modality may depend on the telescope.
   -The telescope needs to be checked in a context divided by the modality.
   HOWEVER: The only information you're using about the context is:
   -The number of variables
   -The vals and modules in scope
   I.e. you're using a context with variables and definitions, but without types and modalities.
   So you should use a special scoping context
   FOR TYPE-CHECKING: the flat modality guarantees that there exists a sensible order.
   The constraint solver will find simply solve constraints.
-}
{-| @'lhs2builder' gamma d rawLHS@ scopes @rawLHS@ to a segment builder. -}
lhs2builder :: MonadScoper mode modty rel sc =>
  Ctx Type mode modty v Void ->
  mode v ->
  Raw.LHS ->
  --sc [Segment Type Type mode modty v]
  sc (SegmentBuilder Type Type mode modty v)
--lhs2builder gamma d lhs = (>>= buildSegment gamma d) . (`execStateT` newSegmentBuilder) $ do
lhs2builder gamma d rawLHS = (`execStateT` newSegmentBuilder) $ do

  -- NAMES
  let rawNames = Raw.namesLHS rawLHS
  {-names <- case Raw.namesLHS lhs of
    Raw.SomeNamesForTelescope names' -> return names'
    Raw.QNameForEntry qname ->
      scopeFail $ "I thought I was scoping a telescope segment, but it was parsed as an entry: " ++ Raw.unparse lhs
    Raw.NoNameForConstraint -> assertFalse "Constraints are abolished."-}
  modify $ \ segBuilder -> segBuilder {segmentBuilderNames = rawNames}

  -- ANNOTATIONS
  {- TODO TODO TODO TODO TODO TODO TODO TODO TODO TODO TODO TODO TODO TODO TODO TODO TODO TODO TODO TODO
     For now, we check the annotations outside of the telescope of the thing they annotate.
     This rules out dependent modes.
  -}
  fineAnnots <- sequenceA $ annotation gamma d <$> Raw.annotationsLHS rawLHS
  forM_ fineAnnots $ \ fineAnnot -> do
    segBuilder <- get
    case fineAnnot of
      AnnotMode d' -> case segmentBuilderMode segBuilder of
        Compose (Just d'') -> scopeFail $ "Encountered multiple mode annotations: " ++ Raw.unparse rawLHS
        Compose Nothing -> modify $ \ segBuilder -> segBuilder {segmentBuilderMode = Compose $ Just d'}
      AnnotModality mu' -> case segmentBuilderModality segBuilder of
        Compose (Just mu'') -> scopeFail $ "Encountered multiple modality annotations: " ++ Raw.unparse rawLHS
        Compose Nothing -> modify $ \ segBuilder -> segBuilder {segmentBuilderModality = Compose $ Just mu'}
      AnnotImplicit -> case segmentBuilderVisibility segBuilder of
        Compose (Just v) -> scopeFail $ "Encountered multiple visibility annotations: " ++ Raw.unparse rawLHS
        Compose Nothing -> modify $ \ segBuilder -> segBuilder {segmentBuilderVisibility = Compose $ Just Implicit}

  -- TELESCOPE AND TYPE (should be checked after dividing the context)
  fineDelta <- telescope gamma d $ Raw.contextLHS rawLHS
  fineTelescopedType <- let f :: forall w .
                              (_ -> w) ->
                              Ctx Type _ _ w Void ->
                              Unit3 _ _ w ->
                              StateT _ _ (Maybe3 Type _ _ w)
                            f = \ wkn gammadelta Unit3 -> case Raw.typeLHS rawLHS of
                              Nothing -> return . Maybe3 . Compose $ Nothing
                              Just rawTy -> Maybe3 . Compose . Just <$> do
                                let d' = wkn <$> d
                                fineLvl <- term4newImplicit gammadelta d'
                                ElTerm fineLvl <$> expr gammadelta d' rawTy
                        in mapTelescoped f gamma fineDelta
  modify $ \ segBuilder -> segBuilder {segmentBuilderTelescopedType = fineTelescopedType}

{-| Chain a list of fine segments to a fine telescope. -}
segments2telescoped :: --MonadScoper mode modty rel sc =>
  (Functor mode, Functor modty) =>
  Ctx Type mode modty v Void ->
  mode v ->
  [Segment Type Type mode modty v] ->
  (Telescoped Type Unit3 mode modty v)
segments2telescoped gamma d [] =
  Telescoped Unit3
segments2telescoped gamma d (fineSeg:fineSegs) =
  fineSeg :|- segments2telescoped (gamma :.. (VarFromCtx <$> fineSeg)) (VarWkn <$> d) (fmap VarWkn <$> fineSegs)

{-| Scope a raw segment to a fine telescope. -}
segment :: MonadScoper mode modty rel sc =>
  Ctx Type mode modty v Void ->
  mode v ->
  Raw.Segment ->
  sc (Telescoped Type Unit3 mode modty v)
segment gamma d (Raw.Segment rawLHS) = do
  segBuilder <- lhs2builder gamma d rawLHS
  segments2telescoped gamma d <$> buildSegment gamma d segBuilder (segmentNamesHandler gamma d)

{-| scope a partly fine, partly raw telescope to a fine telescope. -}
telescope2 :: MonadScoper mode modty rel sc =>
  Ctx Type mode modty v Void ->
  mode v ->
  Telescoped Type Unit3 mode modty v ->
  Raw.Telescope ->
  sc (Telescoped Type Unit3 mode modty v)
telescope2 gamma d (Telescoped Unit3) rawTele = telescope gamma d rawTele
telescope2 gamma d (fineSeg :|- fineSegs) rawTele =
  (fineSeg :|-) <$> telescope2 (gamma :.. (VarFromCtx <$> fineSeg)) (VarWkn <$> d) fineSegs rawTele

{-| Scope a telescope -}
telescope :: MonadScoper mode modty rel sc =>
  Ctx Type mode modty v Void ->
  mode v ->
  Raw.Telescope ->
  sc (Telescoped Type Unit3 mode modty v)
telescope gamma d (Raw.Telescope []) = return $ Telescoped Unit3
telescope gamma d (Raw.Telescope (rawSeg : rawSegs)) = do
  fineFrontSegs <- segment gamma d rawSeg
  telescope2 gamma d fineFrontSegs (Raw.Telescope rawSegs)

----------------------------------------------------------

{-| Scope a raw LHS and a raw value RHS to a value, or fail. -}
val :: MonadScoper mode modty rel sc =>
  Ctx Type mode modty v Void ->
  mode v ->
  Raw.LHS ->
  Raw.RHS ->
  sc (Val mode modty v)
val gamma d rawLHS (Raw.RHSVal rawExpr) = do
  lhsBuilder <- lhs2builder gamma d rawLHS
  [fineLHS] <- buildSegment gamma d lhsBuilder (nestedEntryNamesHandler gamma d)
  let fineTelescopedTy = segmentRHS fineLHS
  fineRHS <- mapTelescoped (
           \ wkn gammadelta fineTy -> do
             fineTm <- expr gammadelta (wkn <$> d) rawExpr
             return $ ValRHS fineTm fineTy
         ) gamma fineTelescopedTy
  return $ fineLHS {segmentRHS = fineRHS}
val gamma d rawLHS rawRHS = scopeFail $ "Not a valid RHS for a 'val': " ++ Raw.unparse rawRHS

{-| @'entryInModule' gamma d fineModule rawEntry@ scopes the entry @rawEntry@ as part of the module @fineModule@ -}
entryInModule :: MonadScoper mode modty rel sc =>
  Ctx Type mode modty v Void ->
  mode v ->
  Raw.Entry ->
  ModuleRHS mode modty v ->
  sc (ModuleRHS mode modty v)
entryInModule gamma d rawEntry fineModule = do
  let gammaModule = gamma :<...> VarFromCtx <$> fineModule
        {-(Left <$> ModuleInScope {
          moduleContramod = ModedContramodality d _confused,
          moduleContents = modul
        })-}
  fineEntry <- entry gammaModule (VarInModule <$> d) rawEntry
  return $ addToModule fineModule fineEntry

{-| @'entriesInModule' gamma d fineModule rawEntry@ scopes @rawEntries@ as part of the module @fineModule@ -}
entriesInModule :: MonadScoper mode modty rel sc =>
  Ctx Type mode modty v Void ->
  mode v ->
  [Raw.Entry] ->
  ModuleRHS mode modty v ->
  sc (ModuleRHS mode modty v)
entriesInModule gamma d rawEntries fineModule = foldl (>>=) (return fineModule) (entryInModule gamma d <$> rawEntries)

{-| @'modul' gamma d rawLHS rawRHS@ scopes the module @<rawLHS> <rawRHS>@ (not the top-level module). -}
modul :: MonadScoper mode modty rel sc =>
  Ctx Type mode modty v Void ->
  mode v ->
  Raw.LHS ->
  Raw.RHS ->
  sc (Module mode modty v)
modul gamma d rawLHS (Raw.RHSModule rawEntries) = do
  lhsBuilder <- lhs2builder gamma d rawLHS
  [fineLHS] <- buildSegment gamma d lhsBuilder (nestedEntryNamesHandler gamma d)
  let fineTelescopedTy = segmentRHS fineLHS
  fineRHS <- mapTelescoped (
           \ wkn gammadelta fineTy -> entriesInModule gammadelta (wkn <$> d) rawEntries newModule
         ) gamma fineTelescopedTy
  return $ fineLHS {segmentRHS = fineRHS}
modul gamma d rawLHS rawRHS = scopeFail $ "Not a valid RHS for a 'val': " ++ Raw.unparse rawRHS

lrEntry :: MonadScoper mode modty rel sc =>
  Ctx Type mode modty v Void ->
  mode v ->
  Raw.LREntry ->
  sc (Entry mode modty v)
lrEntry gamma d (Raw.LREntry Raw.HeaderVal rawLHS rawRHS) = EntryVal <$> val gamma d rawLHS rawRHS
lrEntry gamma d (Raw.LREntry Raw.HeaderModule rawLHS rawRHS) = EntryModule <$> modul gamma d rawLHS rawRHS
lrEntry gamma d rawEntry = scopeFail $ "Nonsensical or unsupported entry: " ++ Raw.unparse rawEntry

entry :: MonadScoper mode modty rel sc =>
  Ctx Type mode modty v Void ->
  mode v ->
  Raw.Entry ->
  sc (Entry mode modty v)
entry gamma d (Raw.EntryLR rawLREntry) = lrEntry gamma d rawLREntry

file :: MonadScoper mode modty rel sc =>
  Ctx Type mode modty v Void ->
  mode v ->
  Raw.File ->
  sc (Entry mode modty v)
file gamma d rawFile = entry gamma d (Raw.file2nestedModules rawFile)
