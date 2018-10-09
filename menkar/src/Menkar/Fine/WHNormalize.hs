module Menkar.Fine.WHNormalize where

import Menkar.Fine.Syntax
import Menkar.Fine.Substitution
import Menkar.Fine.Context
import Data.Void
import Control.Monad.Writer

whnormalizeNV ::
  Ctx Type mode modty v Void ->
  TermNV mode modty v ->
  Type mode modty v ->
  Writer [Int] (Term mode modty v)
whnormalizeNV gamma t@(TermCons _) ty = return . Expr3 $ t   -- Mind glue and weld!
whnormalizeNV gamma (TermElim dmu t es) ty = _normElim
whnormalizeNV gamma t@(TermMeta i depcies) ty = Expr3 t <$ tell [i]
whnormalizeNV gamma (TermQName qname) ty = _normQName
whnormalizeNV gamma (TermSmartElim eliminee eliminators result) ty = whnormalize gamma result ty
whnormalizeNV gamma (TermGoal str result) ty = whnormalize gamma result ty

whnormalize ::
  Ctx Type mode modty v Void ->
  Term mode modty v ->
  Type mode modty v ->
  Writer [Int] (Term mode modty v)
whnormalize gamma (Var3 v) ty = return $ Var3 v
whnormalize gamma (Expr3 t) ty = whnormalizeNV gamma t ty
