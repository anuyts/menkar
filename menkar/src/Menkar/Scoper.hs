{-# LANGUAGE FlexibleContexts, FlexibleInstances, ApplicativeDo, MultiParamTypeClasses #-}

module Menkar.Scoper where

import Prelude hiding (pi)
import Menkar.TCMonad.MonadScoper
import qualified Menkar.Raw as Raw
import Menkar.Fine.Syntax
import Menkar.Fine.Judgement
import Menkar.Fine.Substitution
import Control.Exception.AssertFalse
import Control.Monad.State.Lazy
import Data.Functor.Compose

{- SEARCH FOR TODOS -}

eliminator :: MonadScoper mode modty rel sc =>
  Ctx Type mode modty v ->
  mode v ->
  Raw.Eliminator ->
  sc (SmartEliminator mode modty v)
eliminator gamma d (Raw.ElimEnd argSpec) = return $ SmartElimEnd argSpec
eliminator gamma d (Raw.ElimArg argSpec e) = do
  e' <- expr gamma d e
  return $ SmartElimArg argSpec e'
eliminator gamma d (Raw.ElimProj projSpec) = return $ SmartElimProj projSpec

expr3 :: MonadScoper mode modty rel sc =>
  Ctx Type mode modty v ->
  mode v ->
  Raw.Expr3 ->
  sc (Term mode modty v)
expr3 gamma d (Raw.ExprQName qname) = term4val gamma d qname
expr3 gamma d (Raw.ExprParens e) = expr gamma d e
expr3 gamma d (Raw.ExprNatLiteral n) = todo
expr3 gamma d (Raw.ExprImplicit) = term4newImplicit gamma d

elimination :: MonadScoper mode modty rel sc =>
  Ctx Type mode modty v ->
  mode v ->
  Raw.Elimination ->
  sc (Term mode modty v)
elimination gamma d (Raw.Elimination e elims) = do
  e' <- expr3 gamma d e
  tyE' <- type4newImplicit gamma d
  elims' <- sequenceA (eliminator gamma d <$> elims)
  result' <- term4newImplicit gamma d
  --theMode <- mode4newImplicit gamma
  pushConstraint $ Constraint {
      constraintJudgement = JudSmartElim gamma d e' tyE' elims' result',
      constraintParent = Nothing,
      constraintReason = "Scoper: Elaborate smart elimination."
    }
  return result'

expr2 :: MonadScoper mode modty rel sc =>
  Ctx Type mode modty v ->
  mode v ->
  Raw.Expr2 ->
  sc (Term mode modty v)
expr2 gamma d (Raw.ExprElimination e) = elimination gamma d e

buildPi :: MonadScoper mode modty rel sc =>
  Ctx Type mode modty v ->
  mode v ->
  Segment Type Type mode modty v ->
  Term mode modty (Maybe v) ->
  sc (Term mode modty v)
buildPi gamma d seg cod = do
  lvl <- term4newImplicit gamma d
  return $ Expr $ TermCons $ ConsUnsafeResize d lvl lvl $ Pi $ Binding seg cod

buildSigma :: MonadScoper mode modty rel sc =>
  Ctx Type mode modty v ->
  mode v ->
  Segment Type Type mode modty v ->
  Term mode modty (Maybe v) ->
  sc (Term mode modty v)
buildSigma gamma d seg cod = do
  lvl <- term4newImplicit gamma d
  return $ Expr $ TermCons $ ConsUnsafeResize d lvl lvl $ Sigma $ Binding seg cod
  
buildLambda :: MonadScoper mode modty rel sc =>
  Ctx Type mode modty v ->
  mode v ->
  Segment Type Type mode modty v ->
  Term mode modty (Maybe v) ->
  sc (Term mode modty v)
buildLambda gamma d seg body =
  return $ Expr $ TermCons $ Lam $ Binding seg body

binder2 :: MonadScoper mode modty rel sc =>
  ( forall w .
    Ctx Type mode modty w ->
    mode w ->
    Segment Type Type mode modty w ->
    Term mode modty (Maybe w) ->
    sc (Term mode modty w)
  ) ->
  Ctx Type mode modty v ->
  mode v ->
  Telescoped Type Unit3 mode modty v ->
      {-^ remainder of the already-scoped part of the telescope on the left of the operator -}
  [Raw.Segment] -> {-^ telescope on the left of the operator -}
  Raw.Expr -> {-^ operand on the right of the operator -}
  sc (Term mode modty v)
binder2 build gamma d (Telescoped Unit3) args body = binder build gamma d args body
binder2 build gamma d (seg :|- segs) args body =
  build gamma d seg =<< binder2 build (gamma :.. seg) (Just <$> d) segs args body

binder :: MonadScoper mode modty rel sc =>
  ( forall w .
    Ctx Type mode modty w ->
    mode w ->
    Segment Type Type mode modty w ->
    Term mode modty (Maybe w) ->
    sc (Term mode modty w)
  ) ->
  Ctx Type mode modty v ->
  mode v ->
  [Raw.Segment] -> {-^ telescope on the left of the operator -}
  Raw.Expr -> {-^ operand on the right of the operator -}
  sc (Term mode modty v)
binder build gamma d [] body = expr gamma d body
binder build gamma d (arg:args) body = do
  argTele <- segment gamma d arg
  binder2 build gamma d argTele args body

exprTele :: MonadScoper mode modty rel sc =>
  Ctx Type mode modty v ->
  mode v ->
  Raw.Telescope -> {-^ telescope on the left of the operator -}
  Raw.Elimination -> {-^ the operator -}
  Maybe (Raw.Expr) -> {-^ operand on the right of the operator -}
  sc (Term mode modty v)
exprTele gamma d theta op@(Raw.Elimination _ (_ : _)) maybeER =
  scopeFail $ "Smart eliminations used on a binding operator: " ++ show op
exprTele gamma d theta op@(Raw.Elimination (Raw.ExprQName (Raw.Qualified [] (Raw.Name Raw.Op opname))) []) maybeER =
  case (opname, maybeER) of
    (">", Just body) -> binder buildLambda gamma d (Raw.untelescope theta) body
    ("><", Just cod) -> binder buildSigma gamma d (Raw.untelescope theta) cod
    ("->", Just cod) -> binder buildPi gamma d (Raw.untelescope theta) cod
    (_, Nothing) -> scopeFail $ "Binder body/codomain is missing."
    _    -> scopeFail $ "Illegal operator name: " ++ opname
exprTele gamma d theta op maybeER =
  scopeFail $ "Binding operator is not an unqualified name: " ++ show op

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
{- For now, every operator is right associative with equal precedence -}
expr :: MonadScoper mode modty rel sc =>
  Ctx Type mode modty v ->
  mode v ->
  Raw.Expr ->
  sc (Term mode modty v)
expr gamma d (Raw.ExprOps (Raw.OperandExpr e) Nothing) = expr2 gamma d e
expr gamma d (Raw.ExprOps (Raw.OperandExpr eL) (Just (op, Nothing))) = do
  elimination gamma d (Raw.addEliminators op [Raw.ElimArg Raw.ArgSpecVisible (Raw.expr2to1 eL)])
expr gamma d (Raw.ExprOps (Raw.OperandExpr eL) (Just (op, Just eR))) = do
  elimination gamma d (Raw.addEliminators op [Raw.ElimArg Raw.ArgSpecVisible (Raw.expr2to1 eL),
                                              Raw.ElimArg Raw.ArgSpecVisible eR])
expr gamma d fullExpr@(Raw.ExprOps (Raw.OperandTelescope _) Nothing) =
  scopeFail $ "Naked telescope appears as expression: " ++ show fullExpr
expr gamma d (Raw.ExprOps (Raw.OperandTelescope theta) (Just (op, maybeER))) = exprTele gamma d theta op maybeER

------------------------------------------------

annotation :: MonadScoper mode modty rel sc =>
  Ctx Type mode modty v ->
  mode v ->
  Raw.Annotation ->
  sc (Annotation mode modty v)
annotation gamma d (Raw.Annotation (Raw.Qualified [] "~") []) = return AnnotImplicit
annotation gamma d (Raw.Annotation qstring exprs) = do
  exprs' <- sequenceA $ expr3 gamma d <$> exprs
  annot4annot gamma d qstring exprs'

segment :: MonadScoper mode modty rel sc =>
  Ctx Type mode modty v ->
  mode v ->
  Raw.Segment ->
  sc (Telescoped Type Unit3 mode modty v)
segment gamma d seg = _segment

lhs2segments :: MonadScoper mode modty rel sc =>
  Ctx Type mode modty v ->
  mode v ->
  Raw.LHS ->
  sc [Segment Type Type mode modty v]
lhs2segments gamma d lhs = (`evalStateT` newSegmentBuilder) $ do
  annots <- sequenceA $ annotation gamma d <$> Raw.annotationsLHS lhs
  forM_ annots $ \ annot -> do
    builder <- get
    case annot of
      AnnotMode d' -> case segmentBuilderMode builder of
        Compose (Just d'') -> scopeFail $ "Encountered multiple mode annotations: " ++ show lhs
        Compose Nothing -> modify $ \ builder -> builder {segmentBuilderMode = Compose $ Just d'}
      AnnotModality mu' -> case segmentBuilderModality builder of
        Compose (Just mu'') -> scopeFail $ "Encountered multiple modality annotations: " ++ show lhs
        Compose Nothing -> modify $ \ builder -> builder {segmentBuilderModality = Compose $ Just mu'}
      AnnotImplicit -> case segmentBuilderVisibility builder of
        Compose (Just v) -> scopeFail $ "Encountered multiple visibility annotations: " ++ show lhs
        Compose Nothing -> modify $ \ builder -> builder {segmentBuilderVisibility = Compose $ Just Implicit}
  -- somehow parse context and type
  -- multiply builder for each name (ListT?)
  -- build segment
  _lhs2segments

{- TACKLE THIS THE OTHER WAY AROUND!!!
val :: MonadScoper mode modty rel s => Raw.LHS -> Raw.RHS -> s (Val mode modty v)
val lhs rhs = do
  let Raw.QNameForEntry qname = 
  return Segment {
    segmentInfo = _info,
    segmentModality = _mod,
    segmentType = _type
  }

lrEntry :: MonadScoper mode modty rel s => Raw.LREntry -> s (Entry mode modty v)
lrEntry (Raw.LREntry Raw.HeaderVal lhs rhs) = EntryVal <$> val lhs rhs
lrEntry _ = _lrentry

entry :: MonadScoper mode modty rel s => Raw.Entry -> s (Entry mode modty v)
entry (Raw.EntryLR entry) = lrEntry entry

file :: MonadScoper mode modty rel s => Raw.File -> s (Entry mode modty v)
file (Raw.File entry) = lrEntry entry
-}

