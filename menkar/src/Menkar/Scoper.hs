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
import Control.Lens

{- SEARCH FOR TODOS -}

{-| @'eliminator' gamma rawElim@ scopes @rawElim@ to a fine smart eliminator. -}
eliminator :: MonadScoper mode modty rel sc =>
  ScCtx mode modty v Void ->
  Raw.Eliminator ->
  sc (SmartEliminator mode modty v)
eliminator gamma (Raw.ElimEnd argSpec) = return $ SmartElimEnd argSpec
eliminator gamma (Raw.ElimArg argSpec rawExpr) = do
  fineExpr <- expr gamma rawExpr
  return $ SmartElimArg argSpec fineExpr
eliminator gamma (Raw.ElimProj projSpec) = return $ SmartElimProj projSpec

{-| @'expr3' gamma rawExpr@ scopes @rawExpr@ to a term. -}
expr3 :: MonadScoper mode modty rel sc =>
  ScCtx mode modty v Void ->
  Raw.Expr3 ->
  sc (Term mode modty v)
expr3 gamma (Raw.ExprQName rawQName) = term4val gamma rawQName
expr3 gamma (Raw.ExprParens rawExpr) = expr gamma rawExpr
expr3 gamma (Raw.ExprNatLiteral n) = todo
expr3 gamma (Raw.ExprImplicit) = term4newImplicit gamma

{-| @'elimination' gamma rawElim@ scopes @rawElim@ to a term. -}
elimination :: MonadScoper mode modty rel sc =>
  ScCtx mode modty v Void ->
  Raw.Elimination ->
  sc (Term mode modty v)
elimination gamma (Raw.Elimination rawExpr rawElims) = do
  fineExpr <- expr3 gamma rawExpr
  --fineTy <- type4newImplicit gamma
  fineElims <- sequenceA (eliminator gamma <$> rawElims)
  fineResult <- term4newImplicit gamma
  return . Expr $ TermSmartElim fineExpr (Compose fineElims) fineResult
  --theMode <- mode4newImplicit gamma
  {-pushConstraint $ Constraint {
      constraintJudgement = JudSmartElim gamma fineExpr fineTy fineElims fineResult,
      constraintParent = Nothing,
      constraintReason = "Scoper: Elaborate smart elimination."
    }-}
  --return fineResult

{-| @'expr2' gamma rawExpr@ scopes @rawExpr@ to a term. -}
expr2 :: MonadScoper mode modty rel sc =>
  ScCtx mode modty v Void ->
  Raw.Expr2 ->
  sc (Term mode modty v)
expr2 gamma (Raw.ExprElimination rawElim) = elimination gamma rawElim

--------------------------------------------------

{-| @'simpleLambda' gamma rawArg rawBody@ scopes the Menkar lambda-expression @<rawArg> > <rawBody>@ to a term. -}
simpleLambda :: MonadScoper mode modty rel sc =>
  ScCtx mode modty v Void ->
  Raw.Expr2 ->
  Raw.Expr ->
  sc (Term mode modty v)
simpleLambda gamma rawArg@(Raw.ExprElimination (Raw.Elimination boundArg [])) rawBody =
  do
    d <- mode4newImplicit gamma
    mu <- modty4newImplicit gamma
    fineTy <- type4newImplicit gamma
    maybeName <- case boundArg of
      Raw.ExprQName (Raw.Qualified [] name) -> return $ Just name
      Raw.ExprImplicit -> return $ Nothing
      _ -> scopeFail $
           "To the left of a '>', I expect a telescope, a single unqualified name, or an underscore: " ++ Raw.unparse rawArg
    let fineSeg = Telescoped $ Declaration {
          _decl'name = maybeName,
          _decl'modty = ModedModality d mu,
          _decl'plicity = Explicit,
          _decl'content = fineTy
        }
    fineBody <- expr (gamma ::.. (VarFromCtx <$> segment2scSegment fineSeg)) rawBody
    return . Expr . TermCons . Lam $ Binding fineSeg fineBody
simpleLambda gamma rawArg rawBody =
  scopeFail $
  "To the left of a '>', I expect a telescope, a single unqualified name, or an underscore: " ++ Raw.unparse rawArg

{-| @'buildPi' gamma fineSeg fineCod@ scopes the Menkar expression @<fineSeg> -> <fineCod>@ to a term. -}
buildPi :: MonadScoper mode modty rel sc =>
  ScCtx mode modty v Void ->
  Segment Type mode modty v ->
  Term mode modty (VarExt v) ->
  sc (Term mode modty v)
buildPi gamma fineSeg fineCod = do
  fineLvl <- term4newImplicit gamma
  fineMode <- mode4newImplicit gamma
  return $ Expr $ TermCons $ ConsUnsafeResize fineMode fineLvl fineLvl $ Pi $ Binding fineSeg fineCod

{-| @'buildSigma' gamma fineSeg fineCod@ scopes the Menkar expression @<fineSeg> >< <fineCod>@ to a term. -}
buildSigma :: MonadScoper mode modty rel sc =>
  ScCtx mode modty v Void ->
  Segment Type mode modty v ->
  Term mode modty (VarExt v) ->
  sc (Term mode modty v)
buildSigma gamma fineSeg fineCod = do
  fineLvl <- term4newImplicit gamma
  fineMode <- mode4newImplicit gamma
  return $ Expr $ TermCons $ ConsUnsafeResize fineMode fineLvl fineLvl $ Sigma $ Binding fineSeg fineCod
  
{-| @'buildLambda' gamma fineSeg fineBody@ scopes the Menkar expression @<fineSeg> > <fineBody>@ to a term. -}
buildLambda :: MonadScoper mode modty rel sc =>
  ScCtx mode modty v Void ->
  Segment Type mode modty v ->
  Term mode modty (VarExt v) ->
  sc (Term mode modty v)
buildLambda gamma fineSeg fineCod =
  return $ Expr $ TermCons $ Lam $ Binding fineSeg fineCod

{-| @'binder2' build gamma fineSegs rawArgs rawBody@ scopes the Menkar expression
    @<fineSegs> **> <rawArgs> **> rawBody@ to a term, where
    @build gamma fineSeg fineBody@ scopes the Menkar expression @<fineSeg> **> <fineBody>@ to a term. -}
binder2 :: MonadScoper mode modty rel sc =>
  ( forall w .
    ScCtx mode modty w Void ->
    Segment Type mode modty w ->
    Term mode modty (VarExt w) ->
    sc (Term mode modty w)
  ) ->
  ScCtx mode modty v Void ->
  Telescoped Type Unit3 mode modty v ->
      {-^ remainder of the already-scoped part of the telescope on the left of the operator -}
  [Raw.Segment] -> {-^ telescope on the left of the operator -}
  Raw.Expr -> {-^ operand on the right of the operator -}
  sc (Term mode modty v)
binder2 build gamma (Telescoped Unit3) rawArgs rawBody = binder build gamma rawArgs rawBody
binder2 build gamma (fineSeg :|- fineSegs) rawArgs rawBody =
  build gamma fineSeg =<< binder2 build (gamma ::.. (VarFromCtx <$> segment2scSegment fineSeg)) fineSegs rawArgs rawBody

{-| @'binder' build gamma rawArgs rawBody@ scopes the Menkar expression
    @<rawArgs> **> rawBody@ to a term, where
    @build gamma fineSeg fineBody@ scopes the Menkar expression @<fineSeg> **> <fineBody>@ to a term. -}
binder :: MonadScoper mode modty rel sc =>
  ( forall w .
    ScCtx mode modty w Void ->
    Segment Type mode modty w ->
    Term mode modty (VarExt w) ->
    sc (Term mode modty w)
  ) ->
  ScCtx mode modty v Void ->
  [Raw.Segment] -> {-^ telescope on the left of the operator -}
  Raw.Expr -> {-^ operand on the right of the operator -}
  sc (Term mode modty v)
binder build gamma [] rawBody = expr gamma rawBody
binder build gamma (rawArg:rawArgs) rawBody = do
  fineArgTelescoped <- segment gamma rawArg
  binder2 build gamma fineArgTelescoped rawArgs rawBody

{-| @'telescopeOperation' gamma rawTheta rawOp maybeRawExprR@ scopes the Menkar expression
    @<rawTheta> <rawOp> <maybeRawExprR>@ to a term. -}
telescopeOperation :: MonadScoper mode modty rel sc =>
  ScCtx mode modty v Void ->
  Raw.Telescope -> {-^ telescope on the left of the operator -}
  Raw.Elimination -> {-^ the operator -}
  Maybe (Raw.Expr) -> {-^ operand on the right of the operator -}
  sc (Term mode modty v)
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
    (_, Nothing) -> scopeFail $ "Binder body/codomain is missing."
    _    -> scopeFail $ "Illegal operator name: " ++ opString
telescopeOperation gamma theta rawOp maybeRawExprR =
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
  ScCtx mode modty v ->
  mode v ->
  Raw.Expr ->
  sc (OpTree mode modty v)
exprToTree gamma _ = _exprToTree
-}

{- YOU NEED TO RESOLVE FIXITY HERE -}
{-| @'expr' gamma rawExpr@ scopes @rawExpr@ to a term.
    For now, every operator is right associative with equal precedence. -}
expr :: MonadScoper mode modty rel sc =>
  ScCtx mode modty v Void ->
  Raw.Expr ->
  sc (Term mode modty v)
-- Operator-free expression (e.g. @5@)
expr gamma (Raw.ExprOps (Raw.OperandExpr rawExpr) Nothing) = expr2 gamma rawExpr
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
  elimination gamma (Raw.addEliminators rawOp [Raw.ElimArg Raw.ArgSpecExplicit (Raw.expr2to1 rawExprL)])
-- Binary operator expression (e.g. @a == .{A} b@)
expr gamma (Raw.ExprOps (Raw.OperandExpr rawExprL) (Just (rawOp, Just rawExprR))) = do
  elimination gamma (Raw.addEliminators rawOp [Raw.ElimArg Raw.ArgSpecExplicit (Raw.expr2to1 rawExprL),
                                              Raw.ElimArg Raw.ArgSpecExplicit rawExprR])
-- Naked telescope
expr gamma fullRawExpr@(Raw.ExprOps (Raw.OperandTelescope _) Nothing) =
  scopeFail $ "Naked telescope appears as expression: " ++ Raw.unparse fullRawExpr
-- Operation on telescope
expr gamma (Raw.ExprOps (Raw.OperandTelescope rawTheta) (Just (rawOp, maybeRawExprR))) =
  telescopeOperation gamma rawTheta rawOp maybeRawExprR

------------------------------------------------

{-| @'annotation' gamma rawAnnot@ scopes @rawAnnot@ to an annotation. -}
annotation :: MonadScoper mode modty rel sc =>
  ScCtx mode modty v Void ->
  Raw.Annotation ->
  sc (Annotation mode modty v)
annotation gamma (Raw.Annotation (Raw.Qualified [] "~") []) = return AnnotImplicit
annotation gamma (Raw.Annotation qstring rawExprs) = do
  fineExprs <- sequenceA $ expr3 gamma <$> rawExprs
  annot4annot gamma qstring fineExprs

{-| @'mapTelescoped' f gamma <theta |- rhs>@ yields @<theta |- f wkn (gamma.theta) rhs>@ -}
mapTelescoped :: (Functor h, Functor mode, Functor modty, Functor (ty mode modty)) =>
  (forall w . (v -> w) -> ScCtx mode modty w Void -> rhs1 mode modty w -> h (rhs2 mode modty w)) ->
  (ScCtx mode modty v Void -> Telescoped ty rhs1 mode modty v -> h (Telescoped ty rhs2 mode modty v))
mapTelescoped f gamma (Telescoped rhs) = Telescoped <$> f id gamma rhs
mapTelescoped f gamma (seg :|- stuff) = (seg :|-) <$>
  mapTelescoped (f . (. VarWkn)) (gamma ::.. (VarFromCtx <$> segment2scSegment seg)) stuff

{-
class PresentNames (declSort :: Raw.DeclSort) where
  presentNames :: MonadScoper mode modty rel sc =>
    ScCtx name modty v Void ->
    Raw.DeclNames declSort ->
    [Maybe Raw.Name]
instance PresentNames Raw.DeclSortSegment where
  presentNames gamma (Raw.DeclNamesSegment rawMaybeNames) = rawMaybeNames
instance PresentNames Raw.DeclSortModule where
  presentNames gamma (Raw.DeclNamesModule string) = 

{-| @'segmentNamesHandler' gamma@ fails or maps @'SomeNamesForTelescope' rawNames@ to @rawNames@ -}
segmentNamesHandler :: MonadScoper mode modty rel sc =>
  ScCtx mode modty v Void ->
  Raw.DeclNames Raw.DeclSortSegment ->
  sc [Maybe Raw.Name]
segmentNamesHandler gamma rawDeclNames = case rawDeclNames of
  Raw.DeclNamesSegment rawMaybeNames -> return rawMaybeNames

{-| @'nestedEntryNamesHandler' gamma@ fails or maps @'QNameForEntry' (Qualified [] rawName)@ to @[rawName]@ -}
nestedEntryNamesHandler :: MonadScoper mode modty rel sc =>
  ScCtx mode modty v Void ->
  Raw.LHSNames ->
  sc [Maybe Raw.Name]
nestedEntryNamesHandler gamma rawLHSNames = case rawLHSNames of
    (Raw.SomeNamesForTelescope rawNames) -> 
      assertFalse $ "I thought I was scoping an entry, but it was parsed as a telescope segment: " ++ Raw.unparse rawLHSNames
    Raw.QNameForEntry (Raw.Qualified [] rawName) -> return $ [Just rawName]
    Raw.QNameForEntry rawQName ->
      scopeFail $ "Not supposed to be qualified: " ++ Raw.unparse rawQName
    Raw.NoNameForConstraint -> assertFalse "Constraints are abolished."
-}

{- | @'buildSegment' gamma segBuilder nameHandler@ builds a list of segments out of @segBuilder@.

     For now, arguments written between the same accolads, are required to have the same type.
     The only alternative that yields sensible error messages, is to give them different, interdependent types (as in Agda).
-}
-- You need PARAMETRIZED FINE DECLARATIONS
buildSegment :: MonadScoper mode modty rel sc =>
  ScCtx mode modty v Void ->
  PartialSegment declSort Type mode modty v ->
  --(Raw.DeclNames declSort -> sc [Maybe Raw.Name]) ->
  sc [Segment Type mode modty v]
buildSegment gamma partSeg nameHandler = runListT $ mapTelescoped (
    \ wkn gammadelta partDecl -> do
        -- allocate all implicits BEFORE name fork
        d <- case _pdecl'mode partDecl of
          Compose (Just d') -> return d'
          Compose Nothing -> mode4newImplicit gammadelta
        mu <- case _pdecl'modty partDecl of
          Compose (Just mu') -> return mu'
          Compose Nothing -> modty4newImplicit gammadelta
        let plic = case _pdecl'plicity partDecl of
              Compose (Just plic') -> plic'
              Compose Nothing -> Explicit
        ty <- case _pdecl'content partDecl of
          Compose (Just ty') -> return ty'
          Compose Nothing -> type4newImplicit gammadelta {- TODO adapt this for general telescoped declarations. -}
        name <- ListT . nameHandler $ _pdecl'names partDecl
        return Declaration {
          _decl'name = name,
          _decl'modty = ModedModality d mu,
          _decl'plicity = plic,
          _decl'content = ty
          }
  ) gamma partSeg

  {-do
  -- allocate all implicits BEFORE name fork
  d <- case segmentBuilderMode segBuilder of
    Compose (Just d') -> return d'
    Compose Nothing -> mode4newImplicit gamma
  mu <- case segmentBuilderModality segBuilder of
    Compose (Just mu') -> return mu'
    Compose Nothing -> modty4newImplicit gamma
  let vis = case segmentBuilderPlicity segBuilder of
        Compose (Just vis') -> vis'
        Compose Nothing -> Explicit
  rhs <- mapTelescoped (
           \ wkn gammadelta (Maybe3 (Compose maybeTy)) -> case maybeTy of
               Just ty -> return ty
               Nothing -> type4newImplicit gammadelta
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
      segmentPlicity = vis,
      segmentRHS = rhs,
      segmentRightCartesian = False
    }-}

{-| @'lhs2pseg' gamma rawLHS@ scopes @rawLHS@ to a partial segment. -}
lhs2pseg :: MonadScoper mode modty rel sc =>
  ScCtx mode modty v Void ->
  Raw.LHS ->
  --sc [Segment Type mode modty v]
  sc (PartialSegment Type mode modty v)
lhs2pseg gamma rawLHS = do
  fineDelta <- telescope gamma $ Raw.lhs'context rawLHS
  mapTelescoped (
      \ wkn gammadelta Unit3 -> (`execStateT` newPartialDeclaration) $ do
          --names
          let rawNames = Raw.lhs'names rawLHS
          pdecl'names .= rawNames
          --type
          case Raw.lhs'type rawLHS of
            Nothing -> return ()
            Just rawTy -> do
              fineTy <- do
                fineLvl <- term4newImplicit gammadelta
                ElTerm fineLvl <$> expr gammadelta rawTy
              pdecl'content .= (Compose $ Just $ fineTy)
          --annotations
          fineAnnots <- sequenceA $ annotation gammadelta <$> Raw.lhs'annotations rawLHS
          forM_ fineAnnots $
            \ fineAnnot ->
              case fineAnnot of
                AnnotMode fineMode -> do
                  -- _Wrapped' is a lens for Compose
                  maybeOldFineMode <- use $ pdecl'mode._Wrapped'
                  case maybeOldFineMode of
                    Just oldFineMode -> scopeFail $ "Encountered multiple mode annotations: " ++ Raw.unparse rawLHS
                    Nothing -> pdecl'mode._Wrapped' .= Just fineMode
                AnnotModality fineModty -> do
                  maybeOldFineModty <- use $ pdecl'modty._Wrapped'
                  case maybeOldFineModty of
                    Just oldFineModty -> scopeFail $ "Encountered multiple modality annotations: " ++ Raw.unparse rawLHS
                    Nothing -> pdecl'modty._Wrapped' .= Just fineModty
                AnnotImplicit -> do
                  maybeOldFinePlicity <- use $ pdecl'plicity._Wrapped'
                  case maybeOldFinePlicity of
                    Just oldFinePlicity -> scopeFail $ "Encountered multiple visibility annotations: " ++ Raw.unparse rawLHS
                    Nothing -> pdecl'plicity._Wrapped' .= Just Implicit
    ) gamma fineDelta

{-| Chain a list of fine segments to a fine telescope. -}
segments2telescoped :: --MonadScoper mode modty rel sc =>
  (Functor mode, Functor modty) =>
  ScCtx mode modty v Void ->
  [Segment Type mode modty v] ->
  (Telescoped Type Unit3 mode modty v)
segments2telescoped gamma [] =
  Telescoped Unit3
segments2telescoped gamma (fineSeg:fineSegs) =
  fineSeg :|- segments2telescoped (gamma ::.. (VarFromCtx <$> segment2scSegment fineSeg)) (fmap VarWkn <$> fineSegs)

segment :: MonadScoper mode modty rel sc =>
  ScCtx mode modty v Void ->
  Raw.Segment ->
  sc (Telescoped Type Unit3 mode modty v)
segment gamma (Raw.Segment rawLHS) = do
  partialSeg <- lhs2pseg gamma rawLHS
  segments2telescoped gamma <$> buildSegment gamma partialSeg (segmentNamesHandler gamma)

{-| scope a partly fine, partly raw telescope to a fine telescope. -}
telescope2 :: MonadScoper mode modty rel sc =>
  ScCtx mode modty v Void ->
  Telescoped Type Unit3 mode modty v ->
  Raw.Telescope ->
  sc (Telescoped Type Unit3 mode modty v)
telescope2 gamma (Telescoped Unit3) rawTele = telescope gamma rawTele
telescope2 gamma (fineSeg :|- fineSegs) rawTele =
  (fineSeg :|-) <$> telescope2 (gamma ::.. (VarFromCtx <$> segment2scSegment fineSeg)) fineSegs rawTele

telescope :: MonadScoper mode modty rel sc =>
  ScCtx mode modty v Void ->
  Raw.Telescope ->
  sc (Telescoped Type Unit3 mode modty v)
telescope gamma (Raw.Telescope []) = return $ Telescoped Unit3
telescope gamma (Raw.Telescope (rawSeg : rawSegs)) = do
  fineFrontSegs <- segment gamma rawSeg
  telescope2 gamma fineFrontSegs (Raw.Telescope rawSegs)

----------------------------------------------------------

{-| Scope a raw LHS and a raw value RHS to a value, or fail. -}
val :: MonadScoper mode modty rel sc =>
  ScCtx mode modty v Void ->
  Raw.LHS ->
  Raw.RHS ->
  sc (Val mode modty v)
val gamma rawLHS (Raw.RHSVal rawExpr) = do
  partialSeg <- lhs2pseg gamma rawLHS
  [fineLHS] <- buildSegment gamma partialSeg (nestedEntryNamesHandler gamma)
  mapTelescoped (
      \wkn gammadelta -> decl'content $ \fineTy -> do
        fineTm <- expr gammadelta rawExpr
        return $ ValRHS fineTm fineTy
    ) gamma fineLHS
val gamma rawLHS rawRHS = scopeFail $ "Not a valid RHS for a 'val': " ++ Raw.unparse rawRHS

{-| @'entryInModule' gamma fineModule rawEntry@ scopes the entry @rawEntry@ as part of the module @fineModule@ -}
entryInModule :: MonadScoper mode modty rel sc =>
  ScCtx mode modty v Void ->
  Raw.Entry ->
  ModuleRHS mode modty v ->
  sc (ModuleRHS mode modty v)
entryInModule gamma rawEntry fineModule = do
  let gammaModule = gamma ::<...> VarFromCtx <$> fineModule
        {-(Left <$> ModuleInScope {
          moduleContramod = ModedContramodality d _confused,
          moduleContents = modul
        })-}
  fineEntry <- entry gammaModule rawEntry
  return $ addToModule fineModule fineEntry

{-| @'entriesInModule' gamma fineModule rawEntry@ scopes @rawEntries@ as part of the module @fineModule@ -}
entriesInModule :: MonadScoper mode modty rel sc =>
  ScCtx mode modty v Void ->
  [Raw.Entry] ->
  ModuleRHS mode modty v ->
  sc (ModuleRHS mode modty v)
entriesInModule gamma rawEntries fineModule = foldl (>>=) (return fineModule) (entryInModule gamma <$> rawEntries)

{-| @'modul' gamma rawLHS rawRHS@ scopes the module @<rawLHS> <rawRHS>@ (not the top-level module). -}
modul :: MonadScoper mode modty rel sc =>
  ScCtx mode modty v Void ->
  Raw.LHS ->
  Raw.RHS ->
  sc (Module mode modty v)
modul gamma rawLHS (Raw.RHSModule rawEntries) = do
  partialSeg <- lhs2pseg gamma rawLHS
  [fineLHS] <- buildSegment gamma partialSeg (nestedEntryNamesHandler gamma)
  mapTelescoped (
      --TODO TODO TODO here we want a fineLHS that doesn't have a type!!!
      --This is a bug: every module creates a meta for its type.
      \wkn gammadelta -> decl'content $ \fineTy -> entriesInModule gammadelta rawEntries newModule
    ) gamma fineLHS
modul gamma rawLHS rawRHS = scopeFail $ "Not a valid RHS for a 'val': " ++ Raw.unparse rawRHS

lrEntry :: MonadScoper mode modty rel sc =>
  ScCtx mode modty v Void ->
  Raw.LREntry ->
  sc (Entry mode modty v)
lrEntry gamma (Raw.LREntry Raw.HeaderVal rawLHS rawRHS) = EntryVal <$> val gamma rawLHS rawRHS
lrEntry gamma (Raw.LREntry Raw.HeaderModule rawLHS rawRHS) = EntryModule <$> modul gamma rawLHS rawRHS
lrEntry gamma rawEntry = scopeFail $ "Nonsensical or unsupported entry: " ++ Raw.unparse rawEntry

entry :: MonadScoper mode modty rel sc =>
  ScCtx mode modty v Void ->
  Raw.Entry ->
  sc (Entry mode modty v)
entry gamma (Raw.EntryLR rawLREntry) = lrEntry gamma rawLREntry

file :: MonadScoper mode modty rel sc =>
  ScCtx mode modty v Void ->
  Raw.File ->
  sc (Entry mode modty v)
file gamma rawFile = entry gamma (Raw.file2nestedModules rawFile)
