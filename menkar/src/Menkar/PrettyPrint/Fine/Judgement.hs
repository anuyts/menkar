{-# LANGUAGE UndecidableInstances #-}

module Menkar.PrettyPrint.Fine.Judgement where

import Menkar.Fine.Syntax
import Menkar.Basic.Context
import Menkar.Fine.Context
import Menkar.Fine.Judgement
import Menkar.PrettyPrint.Aux.Context
import qualified Menkar.Raw as Raw
import qualified Menkar.PrettyPrint.Raw as Raw
import Text.PrettyPrint.Tree
import Menkar.PrettyPrint.Fine.Syntax
import Menkar.PrettyPrint.Fine.Context

import Data.Void
import Data.Maybe
import Data.Proxy
import Control.Exception.AssertFalse
import Data.Functor.Compose
import Data.Functor.Const
import Control.Lens

vdash = '\x22A2'
vdash_ = vdash : " "

jud2pretty :: forall mode modty rel .
  (Functor mode, Functor modty,
   Fine2Pretty mode modty Mode, Fine2Pretty mode modty Modty) =>
  Judgement mode modty rel -> PrettyTree String
jud2pretty (JudType gamma ty) =
  ctx2pretty gamma \\\ [vdash_ ++| fine2pretty (ctx2scCtx gamma) ty]
jud2pretty (JudTypeRel deg gamma (Pair3 ty1 ty2)) =
  ctx2pretty gamma \\\ [vdash_ ++| fine2pretty (ctx2scCtx gamma) ty1 |++ " =[]= " |+| fine2pretty (ctx2scCtx gamma) ty2]
  -- CMODE print the degree
jud2pretty (JudTerm gamma t ty) =
  ctx2pretty gamma \\\ [
    vdash_ ++| fine2pretty (ctx2scCtx gamma) t,
    ": " ++| fine2pretty (ctx2scCtx gamma) ty]
jud2pretty (JudTermRel deg gamma (Pair3 t1 t2) ty) =
  ctx2pretty gamma \\\ [
    vdash_ ++| fine2pretty (ctx2scCtx gamma) t1 |++ " =[]= " |+| fine2pretty (ctx2scCtx gamma) t2,
    ": " ++| fine2pretty (ctx2scCtx gamma) ty]
  -- CMODE print the degree
jud2pretty (JudEta gamma t ty) =
  ctx2pretty gamma \\\ [
    vdash_ ++| fine2pretty (ctx2scCtx gamma) t |++ " = eta-expansion",
    ": " ++| fine2pretty (ctx2scCtx gamma) ty]
jud2pretty (JudSmartElim gamma dnu eliminee tyEliminee eliminators result tyResult) =
  ctx2pretty gamma \\\ [
    ribbon (vdash_ ++ "(") \\\ [
      fine2pretty (ctx2scCtx gamma) eliminee,
      ": " ++| fine2pretty (ctx2scCtx gamma) tyEliminee
      ]
    /+/ ribbon ")" \\\ (fine2pretty (ctx2scCtx gamma) <$> eliminators),
    ribbon (charYielding : " (") \\\ [
      fine2pretty (ctx2scCtx gamma) result,
      ": " ++| fine2pretty (ctx2scCtx gamma) tyResult
      ]
    ]
jud2pretty (JudGoal gamma goalName t ty) =
  ctx2pretty gamma \\\ [
    vdash_ ++ goalName ++ " " ++ [charYielding] ++| fine2pretty (ctx2scCtx gamma) t,
    ": " ++| fine2pretty (ctx2scCtx gamma) ty]
jud2pretty (JudResolve gamma t ty) = todo
jud2pretty (JudSegment gamma seg) = ctx2pretty gamma \\\ [vdash_ ++| fine2pretty (ctx2scCtx gamma) seg]
jud2pretty (JudVal gamma val) = ctx2pretty gamma \\\ [vdash : "val " ++| fine2pretty (ctx2scCtx gamma) val]
jud2pretty (JudModule gamma modul) = ctx2pretty gamma \\\ [vdash : "module " ++| fine2pretty (ctx2scCtx gamma) modul]
jud2pretty (JudEntry gamma entry) = ctx2pretty gamma \\\ [vdash : "declaration " ++| fine2pretty (ctx2scCtx gamma) entry]
--jud2pretty jud = _jud2pretty

instance (Functor mode, Functor modty,
          Fine2Pretty mode modty Mode, Fine2Pretty mode modty Modty)
         => Show (Judgement mode modty rel) where
  show jud = render (RenderState 100 "  " "    ") $ jud2pretty jud
