{-# LANGUAGE UndecidableInstances #-}

module Menkar.PrettyPrint.Fine.Judgement where

import Menkar.Fine.Syntax
import Menkar.Basic.Context
import Menkar.Fine.Context
import Menkar.Fine.Judgement
import Menkar.PrettyPrint.Aux.Context
import qualified Menkar.Raw as Raw
import qualified Menkar.PrettyPrint.Raw as Raw
import Menkar.PrettyPrint.Fine.Syntax
import Menkar.PrettyPrint.Fine.Context

import Text.PrettyPrint.Tree
import Data.Omissible

import Data.Void
import Data.Maybe
import Data.Proxy
import Control.Exception.AssertFalse
import Data.Functor.Compose
import Data.Functor.Const
import Control.Lens

vdash = '\x22A2'
vdash_ = vdash : " "
_vdash = [' ', vdash]
_vdash_ = [' ', vdash, ' ']

jud2pretty :: forall sys .
  (SysTrav sys,
   Fine2Pretty sys (Mode sys), Fine2Pretty sys (Modality sys)) =>
  Judgement sys -> Fine2PrettyOptions sys -> PrettyTree String
jud2pretty (JudType gamma ty) opts =
  ctx2pretty gamma opts \\\ [_vdash ++ " <type> " ++| fine2pretty (ctx2scCtx gamma) ty opts]
jud2pretty (JudTypeRel deg gamma (Twice2 ty1 ty2)) opts =
  ctx2pretty gamma opts \\\ [_vdash ++ " <type> " ++| fine2pretty (ctx2scCtx gamma) (Twice2 ty1 ty2) opts]
  -- CMODE print the degree
jud2pretty (JudTerm gamma t ty) opts =
  ctx2pretty gamma opts \\\ [
    _vdash_ ++| fine2pretty (ctx2scCtx gamma) t opts,
    " : " ++| fine2pretty (ctx2scCtx gamma) ty opts]
jud2pretty (JudTermRel deg gamma (Twice2 t1 t2) ty) opts =
  ctx2pretty gamma opts \\\ [
    _vdash_ ++| fine2pretty (ctx2scCtx gamma) (Twice2 t1 t2) opts,
    " : " ++| fine2pretty (ctx2scCtx gamma) ty opts]
  -- CMODE print the degree
jud2pretty (JudEta gamma t ty) opts =
  ctx2pretty gamma opts \\\ [
    _vdash_ ++| fine2pretty (ctx2scCtx gamma) t opts |++ " = eta-expansion",
    " : " ++| fine2pretty (ctx2scCtx gamma) ty opts]
jud2pretty (JudSmartElim gamma dnu eliminee tyEliminee eliminators result tyResult) opts =
  ctx2pretty gamma opts \\\ [
    ribbon _vdash_ \\\ [
      fine2pretty (ctx2scCtx gamma) eliminee opts,
      " : " ++| fine2pretty (ctx2scCtx gamma) tyEliminee opts
      ],
    ribbon " <eliminated-with>" \\\
      ((" " ++|) . ($ opts) . fine2pretty (ctx2scCtx gamma) <$> eliminators),
    ribbon (" <yields> ") \\\ [
      fine2pretty (ctx2scCtx gamma) result opts,
      " : " ++| fine2pretty (ctx2scCtx gamma) tyResult opts
      ]
    ]
jud2pretty (JudGoal gamma goalName t ty) opts =
  ctx2pretty gamma opts \\\ [
    _vdash_ ++ "?" ++ goalName ++ " <takes-value> " ++| fine2pretty (ctx2scCtx gamma) t opts,
    " : " ++| fine2pretty (ctx2scCtx gamma) ty opts]
jud2pretty (JudResolve gamma t ty) opts = todo
jud2pretty (JudSegment gamma seg) opts = ctx2pretty gamma opts \\\ [_vdash ++ " <segment> " ++| fine2pretty (ctx2scCtx gamma) seg opts]
jud2pretty (JudVal gamma val) opts = ctx2pretty gamma opts \\\ [_vdash ++ " <val> " ++| fine2pretty (ctx2scCtx gamma) val opts]
jud2pretty (JudModule gamma modul) opts = ctx2pretty gamma opts \\\ [_vdash ++ " <module> " ++| fine2pretty (ctx2scCtx gamma) modul opts]
jud2pretty (JudEntry gamma entry) opts = ctx2pretty gamma opts \\\ [_vdash ++ " <declaration> " ++| fine2pretty (ctx2scCtx gamma) entry opts]
--jud2pretty jud = _jud2pretty

instance (SysTrav sys,
          Fine2Pretty sys (Mode sys), Fine2Pretty sys (Modality sys))
         => Show (Judgement sys) where
  show jud = render (jud2pretty jud $? id) $? id
