module Menkar.Fine.Unscoper where

import Menkar.Fine.Syntax
import Menkar.Fine.Context
import Menkar.Fine.Substitution
import qualified Menkar.Raw as Raw
import Data.Void

class Unscopable f r where
  unscope :: ScCtx mode modty v void -> f v -> r

class Unscopable f r => Rescopable f r | f -> r where
  unscope' :: ScCtx mode modty v void -> f v -> r
  unscope' = unscope
  scoperName :: f v -> String -> String
  showUnscopable :: ScCtx mode modty v void -> f v -> String
  default showUnscopable :: (Show r) => ScCtx mode modty v void -> f v -> String
  --TODO: explicitly print context? Or not?
  --TODO: this is in fact ill-typed: you still need to extract from scoper monad.
  showUnscopable gamma x = scoperName x "<context>" ++ " $ " ++ (show $ unscope' gamma x)
  
--------------------------------------------

instance (Unscopable mode Raw.Expr3, Unscopable modty Raw.Expr3) =>
         Unscopable (SmartEliminator mode modty) Raw.Eliminator where
  unscope gamma (SmartElimEnd argSpec) = Raw.ElimEnd argSpec
  unscope gamma (SmartElimArg argSpec arg) = Raw.ElimArg argSpec (Raw.expr2to1 $ unscope gamma arg)
  unscope gamma (SmartElimProj projSpec) = Raw.ElimProj projSpec
instance (Unscopable mode Raw.Expr3, Unscopable modty Raw.Expr3) =>
         Rescopable (SmartEliminator mode modty) Raw.Eliminator where
  scoperName _ showGamma = "eliminator " ++ showGamma

instance (Unscopable mode Raw.Expr3, Unscopable modty Raw.Expr3) =>
         Unscopable (TypeTerm mode modty) Raw.Expr3 where
  unscope gamma (UniHS mode lvl) =
    Raw.ExprParens $ Raw.expr2to1 $ Raw.ExprElimination $
    Raw.Elimination (Raw.ExprQName $ Raw.Qualified [] $ Raw.Name Raw.NonOp "UniHS")
      [Raw.ElimArg Raw.ArgSpecExplicit (Raw.expr3to1 $ unscope gamma mode),
       Raw.ElimArg Raw.ArgSpecExplicit (Raw.expr3to1 $ unscope gamma lvl)]
  unscope gamma t = _typeTerm

instance (Unscopable mode Raw.Expr3, Unscopable modty Raw.Expr3) =>
         Unscopable (ConstructorTerm mode modty) Raw.Expr3 where
  unscope gamma (ConsUniHS mode ty) = Raw.ExprParens $
    Raw.ExprOps (Raw.OperandExpr $ Raw.expr3to2 $ unscope gamma ty) $
    Just (
      Raw.Elimination (Raw.ExprQName $ Raw.Qualified [] $ Raw.Name Raw.NonOp "ofMode") [],
      Just $ Raw.expr3to1 $ unscope gamma mode
    )
  unscope gamma t = _constructorTerm

instance (Unscopable mode Raw.Expr3, Unscopable modty Raw.Expr3) =>
         Unscopable (TermNV mode modty) Raw.Expr3 where
  unscope gamma t = _termNV

instance (Unscopable mode Raw.Expr3, Unscopable modty Raw.Expr3) =>
         Unscopable (Term mode modty) Raw.Expr3 where
  unscope gamma (Var3 v) = case scGetName gamma v of
    Just name -> Raw.ExprQName $ Raw.Qualified [] name
    Nothing -> Raw.ExprImplicit
  unscope gamma (Expr3 t) = unscope gamma t
instance (Unscopable mode Raw.Expr3, Unscopable modty Raw.Expr3) =>
         Rescopable (Term mode modty) Raw.Expr3 where
  scoperName _ showGamma = "expr3 " ++ showGamma
instance (Unscopable mode Raw.Expr3, Unscopable modty Raw.Expr3) =>
         Unscopable (Term mode modty) Raw.Expr2 where
  unscope gamma e = Raw.expr3to2 $ unscope gamma e

--------------------------------------------

deriving instance (Show (mode v), Show (modty v)) => Show (ModedModality mode modty v)
deriving instance (Show (mode v), Show (modty v)) => Show (ModedContramodality mode modty v)
--show binding
--show typeterm
--show constructorterm
--show smarteliminator
--show eliminator
--show type
--show termnv
