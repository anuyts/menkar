{-# LANGUAGE FlexibleContexts, FlexibleInstances, ApplicativeDo, MultiParamTypeClasses #-}

module Menkar.Scoper where

import Menkar.TCMonad.MonadScoper
import qualified Menkar.Raw.Syntax as Raw
import Menkar.Fine.Syntax
import Menkar.Fine.Judgement
import Menkar.Fine.Substitution
import Control.Exception.AssertFalse

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

exprTele :: MonadScoper mode modty rel sc =>
  Ctx Type mode modty v ->
  mode v ->
  Raw.Telescope -> {-^ telescope on the left of the operator -}
  Raw.Elimination -> {-^ the operator -}
  Maybe (Raw.Expr) -> {-^ operand on the right of the operator -}
  sc (Term mode modty v)
exprTele gamma d theta op maybeER = _exprTele

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
expr gamma d (Raw.ExprOps (Raw.OperandTelescope _) Nothing) = assertFalse "Naked telescope appears as expression."
expr gamma d (Raw.ExprOps (Raw.OperandTelescope theta) (Just (op, maybeER))) = exprTele gamma d theta op maybeER

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

