{-# LANGUAGE UndecidableInstances #-}

module Menkar.PrettyPrint.Fine.Judgement where

import Menkar.Fine.Syntax
import Menkar.Basic.Context
import Menkar.Fine.Context
import Menkar.Fine.Judgement
import Menkar.System.Fine
import Menkar.System.PrettyPrint
import Menkar.PrettyPrint.Aux.Context
import qualified Menkar.Raw as Raw
import qualified Menkar.PrettyPrint.Raw as Raw
import Menkar.PrettyPrint.Fine.Class
import Menkar.PrettyPrint.Fine.Syntax
import Menkar.PrettyPrint.Fine.Context
import Menkar.Analyzer.Class

import Text.PrettyPrint.Tree
import Data.Omissible
import Data.Functor.Functor1

import Data.Void
import Data.Maybe
import Data.Proxy
import Control.Exception.AssertFalse
import Data.Functor.Compose
import Data.Functor.Const
import Control.Lens
import GHC.Generics

vdash = '\x22A2'
vdash_ = vdash : " "
_vdash = [' ', vdash]
_vdash_ = [' ', vdash, ' ']

haveFine2Pretty :: forall sys t a .
  (SysPretty sys) =>
  AnalyzableToken sys t ->
  ((Fine2Pretty sys t) => a) ->
  a
haveFine2Pretty token a = case token of
  AnTokenModedModality -> a
  AnTokenBinding token -> haveFine2Pretty token a
  AnTokenNamedBinding token -> haveFine2Pretty token a
  AnTokenUniHSConstructor -> a
  AnTokenConstructorTerm -> a
  AnTokenType -> a
  AnTokenDependentEliminator -> a
  AnTokenEliminator -> a
  AnTokenTermNV -> a
  AnTokenTerm -> a
  AnTokenDeclaration token -> a
  AnTokenTelescoped token -> a
  AnTokenValRHS -> a
  AnTokenModuleRHS -> a
  AnTokenEntry -> a
  AnTokenU1 -> a
  AnTokenPair1 ltoken rtoken -> haveFine2Pretty ltoken $ haveFine2Pretty rtoken $ a
  AnTokenConst1 token -> haveFine2Pretty token a
  AnTokenSys systoken -> sysHaveFine2Pretty systoken a

token2string :: forall sys t . (SysPretty sys) => AnalyzableToken sys t -> String
token2string token = case token of
  AnTokenModedModality -> "modality"
  AnTokenBinding token -> "binding:" ++ token2string token
  AnTokenNamedBinding token -> "name-only-binding:" ++ token2string token
  AnTokenUniHSConstructor -> "UniHS-constructor"
  AnTokenConstructorTerm -> "constructor"
  AnTokenType -> "type"
  AnTokenDependentEliminator -> "elimination-clauses"
  AnTokenEliminator -> "eliminator"
  AnTokenTermNV -> "non-variable"
  AnTokenTerm -> "term"
  AnTokenDeclaration token -> "declaration/segment"
  AnTokenTelescoped token -> "telescoped:" ++ token2string token
  AnTokenValRHS -> "typed-term"
  AnTokenModuleRHS -> "module-definition"
  AnTokenEntry -> "entry"
  AnTokenU1 -> "0-tuple"
  AnTokenPair1 ltoken rtoken -> "pair:(" ++ token2string ltoken ++ ", " ++ token2string rtoken ++ ")"
  AnTokenConst1 token -> "const-boxed:" ++ token2string token
  AnTokenSys systoken -> "system-boxed:" ++ sysToken2string systoken

modrel2pretty :: ModRel -> PrettyTree String
modrel2pretty ModLeq = ribbon "\8804"
modrel2pretty ModEq  = ribbon "="

relation2pretty :: forall sys t v .
  (DeBruijnLevel v, Multimode sys, SysPretty sys, Analyzable sys t) =>
  AnalyzableToken sys t ->
  ScCtx sys v Void ->
  ClassifExtraInput t v ->
  ClassifExtraInput t v ->
  Relation t v ->
  Fine2PrettyOptions sys ->
  PrettyTree String
relation2pretty token gamma extraT1 extraT2 relT opts = case (token, relT) of
  (AnTokenModedModality, Const modrel) -> modrel2pretty modrel
  (AnTokenBinding token, ddeg) -> "[" ++| fine2pretty gamma ddeg opts |++ "]"
  (AnTokenNamedBinding token, Comp1 rel) ->
    let seg1 :*: Comp1 extraBody1 = extraT1
        seg2 :*: Comp1 extraBody2 = extraT2
    in  -- it would be cleaner to actually print the variable binding here.
        relation2pretty token (gamma ::.. VarFromCtx <$> segment2scSegment seg1) extraBody1 extraBody2 rel opts
  (AnTokenUniHSConstructor, ddeg) -> "[" ++| fine2pretty gamma ddeg opts |++ "]"
  (AnTokenConstructorTerm, ddeg) -> "[" ++| fine2pretty gamma ddeg opts |++ "]"
  (AnTokenType, ddeg) -> "[" ++| fine2pretty gamma ddeg opts |++ "]"
  (AnTokenDependentEliminator, ddeg) -> "[" ++| fine2pretty gamma ddeg opts |++ "]"
  (AnTokenEliminator, ddeg) -> "[" ++| fine2pretty gamma ddeg opts |++ "]"
  (AnTokenTermNV, ddeg) -> "[" ++| fine2pretty gamma ddeg opts |++ "]"
  (AnTokenTerm, ddeg) -> "[" ++| fine2pretty gamma ddeg opts |++ "]"
  (AnTokenDeclaration token, rel) -> relation2pretty token gamma extraT1 extraT2 rel opts
  (AnTokenTelescoped token, relTy :*: relRHS) ->
    relation2pretty AnTokenType gamma U1 U1 relTy opts |++ "|-" |+|
    relation2pretty token gamma U1 U1 relRHS opts
  (AnTokenValRHS, ddeg) -> "[" ++| fine2pretty gamma ddeg opts |++ "]"
  (AnTokenModuleRHS, ddeg) -> "[" ++| fine2pretty gamma ddeg opts |++ "]"
  (AnTokenEntry, ddeg) -> "[" ++| fine2pretty gamma ddeg opts |++ "]"
  (AnTokenU1, U1) -> ribbon "[]"
  (AnTokenPair1 tokenL tokenR, relL :*: relR) ->
    relation2pretty tokenL gamma (fst1 extraT1) (fst1 extraT2) relL opts |++ "," |+|
    relation2pretty tokenR gamma (snd1 extraT1) (snd1 extraT2) relR opts
  (AnTokenConst1 token, rel) -> relation2pretty token gamma extraT1 extraT2 rel opts

classif2pretty :: forall sys t v .
  (DeBruijnLevel v, Multimode sys, SysPretty sys, Analyzable sys t) =>
  AnalyzableToken sys t ->
  ScCtx sys v Void ->
  ClassifExtraInput t v ->
  Classif t v ->
  ClassifExtraInput (Classif t) v ->
  Fine2PrettyOptions sys ->
  PrettyTree String
classif2pretty token gamma extraT ct extraCT opts =
  case (token, extraT, ct, extraCT) of
    (AnTokenModedModality, U1, dom :*: cod, _) ->
      fine2pretty gamma dom opts
      |++ " -> " |+|
      fine2pretty gamma cod opts
    (AnTokenBinding token, U1, _ :*: boundCRHS, _ :*: seg :*: Comp1 extraCRHS) ->
      "_ -> " ++| classif2pretty token
        (gamma ::.. ScSegment (_namedBinding'name boundCRHS))
        U1 (getConst1 $ _namedBinding'body boundCRHS) extraCRHS opts
    (AnTokenNamedBinding token, seg :*: Comp1 extraRHS, boundCRHS, seg' :*: Comp1 extraCRHS) ->
      "_ -> " ++| classif2pretty token
        (gamma ::.. ScSegment (_namedBinding'name boundCRHS))
        extraRHS (getConst1 $ _namedBinding'body boundCRHS) extraCRHS opts
    (AnTokenUniHSConstructor, U1, d, U1) -> "UniHS " ++| fine2pretty gamma d opts
    (AnTokenConstructorTerm, U1, ty, U1) -> fine2pretty gamma ty opts
    (AnTokenType, U1, U1, U1) -> ribbon "<n/a>"
    (AnTokenDependentEliminator, dmuElim :*: eliminee :*: tyEliminee :*: Comp1 motive, U1, U1) ->
      fine2pretty gamma (Binding (Declaration (DeclNameSegment Nothing) dmuElim Explicit (hs2type tyEliminee)) motive) opts
    (AnTokenEliminator, dmuElim :*: eliminee :*: tyEliminee, tyResult, U1) ->
      ribbon "<eliminate> " \\\
        [fine2pretty gamma eliminee opts] ///
      ribbon " <of-type> " \\\
        [fine2pretty gamma (Declaration (DeclNameSegment Nothing) dmuElim Explicit (hs2type tyEliminee)) opts] ///
      ribbon " <to> " \\\
        [fine2pretty gamma tyEliminee opts]
    (AnTokenTermNV, U1, ty, U1) -> fine2pretty gamma ty opts
    (AnTokenTerm, U1, ty, U1) -> fine2pretty gamma ty opts
    (AnTokenDeclaration token, extraRHS, crhs, extraCRHS) -> classif2pretty token gamma extraRHS crhs extraCRHS opts
    (AnTokenTelescoped token, U1, U1, U1) -> ribbon "<n/a>"
    (AnTokenValRHS, U1, U1, U1) -> ribbon "<n/a>"
    (AnTokenModuleRHS, U1, U1, U1) -> ribbon "<n/a>"
    (AnTokenEntry, U1, U1, U1) -> ribbon "<n/a>"
    (AnTokenU1, U1, U1, U1) -> ribbon "<n/a>"
    (AnTokenPair1 tokenL tokenR, extraL :*: extraR, cl :*: cr, extraCL :*: extraCR) ->
      ribbon "("  \\\ [classif2pretty tokenL gamma extraL cl extraCL opts] ///
      ribbon ", " \\\ [classif2pretty tokenR gamma extraR cr extraCR opts] ///
      ribbon ")"
    (AnTokenConst1 token, extraT, ct, extraCT) -> classif2pretty token gamma extraT ct extraCT opts
    (AnTokenSys systoken, extraT, ct, extraCT) -> sysClassif2pretty systoken gamma extraT ct extraCT opts
    

maybeClassif2pretty :: forall sys t v .
  (DeBruijnLevel v, Multimode sys, SysPretty sys, Analyzable sys t) =>
  AnalyzableToken sys t ->
  ScCtx sys v Void ->
  ClassifExtraInput t v ->
  ClassifInfo (Classif t v) ->
  ClassifExtraInput (Classif t) v ->
  Fine2PrettyOptions sys ->
  PrettyTree String
maybeClassif2pretty token gamma extraT (ClassifWillBe ct) extraCT opts =
  ":. " ++| classif2pretty token gamma extraT ct extraCT opts
maybeClassif2pretty token gamma extraT (ClassifMustBe ct) extraCT opts =
  ":! " ++| classif2pretty token gamma extraT ct extraCT opts
maybeClassif2pretty token gamma extraT (ClassifUnknown) extraCT opts = ribbon ":_"

classification2pretty :: forall sys t v .
  (DeBruijnLevel v, Multimode sys, SysPretty sys, Analyzable sys t, Fine2Pretty sys t) =>
  ScCtx sys v Void ->
  Classification t v ->
  Fine2PrettyOptions sys ->
  PrettyTree String
classification2pretty gamma (Classification t extraT maybeCT) opts =
  let token = analyzableToken @sys @t
  in  "<" ++ token2string token ++ "> " ++| fine2pretty gamma t opts
      |++ " " |+| maybeClassif2pretty token gamma extraT maybeCT (extraClassif @sys t extraT) opts
         
jud2pretty :: forall sys .
  (Multimode sys,
   SysPretty sys) =>
  Judgement sys ->
  Fine2PrettyOptions sys ->
  PrettyTree String
jud2pretty (Jud token gamma t extraT maybeCT) opts = haveFine2Pretty token $
  ctx2pretty gamma opts \\\ [_vdash_ ++| classification2pretty (ctx2scCtx gamma) (Classification t extraT maybeCT) opts]
jud2pretty (JudRel token eta relT gamma (Twice1 t1 t2) (Twice1 extraT1 extraT2) maybeCTs) opts = haveFine2Pretty token $
  ctx2pretty gamma opts \\\ [
    ribbon (_vdash_ ++ (if unEta eta then "" else "<no-eta> ")) \\\
      ["(" ++| classification2pretty (ctx2scCtx gamma) (Classification t1 extraT1 (fstTwice1 <$> maybeCTs)) opts |++ ")",
       relation2pretty token (ctx2scCtx gamma) extraT1 extraT2 relT opts,
       "(" ++| classification2pretty (ctx2scCtx gamma) (Classification t2 extraT2 (sndTwice1 <$> maybeCTs)) opts |++ ")"
      ]
  ]
jud2pretty (JudEta gamma t ty) opts =
  ctx2pretty gamma opts \\\ [
    _vdash_ ++| fine2pretty (ctx2scCtx gamma) t opts |++ " = eta-expansion",
    " : " ++| fine2pretty (ctx2scCtx gamma) ty opts]
jud2pretty (JudSmartElim gamma eliminee tyEliminee eliminators result tyResult) opts =
  ctx2pretty gamma opts \\\ [
    ribbon _vdash_ \\\ [
      fine2pretty (ctx2scCtx gamma) eliminee opts,
      " : " ++| fine2pretty (ctx2scCtx gamma) tyEliminee opts
      ],
    ribbon " <eliminated-with>" \\\
      (eliminators <&> \(Pair2 dmu elim) ->
          " " ++| fine2pretty (ctx2scCtx gamma) dmu opts |++ " " |+| fine2pretty (ctx2scCtx gamma) elim opts
      ),
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
jud2pretty (JudSys jud) opts = sysJud2pretty jud opts


{-
jud2pretty (JudType gamma ty) opts =
  ctx2pretty gamma opts \\\ [_vdash ++ " <type> " ++| fine2pretty (ctx2scCtx gamma) ty opts]
jud2pretty (JudTypeRel deg gamma (Twice2 ty1 ty2)) opts =
  ctx2pretty gamma opts \\\ [_vdash ++ " <type> " ++| fine2pretty (ctx2scCtx gamma) (Twice2 ty1 ty2) opts]
  -- CMODE print the degree
jud2pretty (JudTerm gamma t ty) opts =
  ctx2pretty gamma opts \\\ [
    _vdash_ ++| fine2pretty (ctx2scCtx gamma) t opts,
    " : " ++| fine2pretty (ctx2scCtx gamma) ty opts]
jud2pretty (JudTermRel eta deg gamma (Twice2 t1 t2) ty) opts =
  ctx2pretty gamma opts \\\ [
    _vdash_ ++ (if unEta eta then "" else "<no-eta> ") ++| fine2pretty (ctx2scCtx gamma) (Twice2 t1 t2) opts,
    " : " ++| fine2pretty (ctx2scCtx gamma) ty opts]
  -- CMODE print the degree
jud2pretty (JudMode gamma d) opts =
  ctx2pretty gamma opts \\\ [_vdash ++ " <mode> " ++| fine2pretty (ctx2scCtx gamma) d opts]
jud2pretty (JudModeRel gamma d1 d2) opts =
  ctx2pretty gamma opts \\\ [_vdash ++ " <mode> " ++| twice2pretty (ctx2scCtx gamma) d1 d2 opts]
jud2pretty (JudModality gamma mu ddom dcod) opts =
  ctx2pretty gamma opts \\\ [
    _vdash ++ " <modty> " ++| fine2pretty (ctx2scCtx gamma) mu opts,
    " : " ++| (ribbonEmpty \\\ [
                  fine2pretty (ctx2scCtx gamma) ddom opts,
                  ribbon " => ",
                  fine2pretty (ctx2scCtx gamma) dcod opts])
    ]
jud2pretty (JudModalityRel modrel gamma mu1 mu2 ddom dcod) opts =
  ctx2pretty gamma opts \\\ [
    _vdash ++ " <modty> " ++| (ribbonEmpty \\\ [
                  fine2pretty (ctx2scCtx gamma) mu1 opts,
                  ribbon modrelsign,
                  fine2pretty (ctx2scCtx gamma) mu2 opts]),
    " : " ++| (ribbonEmpty \\\ [
                  fine2pretty (ctx2scCtx gamma) ddom opts,
                  ribbon " => ",
                  fine2pretty (ctx2scCtx gamma) dcod opts])
    ]
  where modrelsign = case modrel of
          ModEq -> " = "
          ModLeq -> " =< "
jud2pretty (JudModedModality gamma (ModedModality ddom mu) dcod) opts =
  ctx2pretty gamma opts \\\ [
    _vdash ++ " <mode;modty> " ++| fine2pretty (ctx2scCtx gamma) mu opts,
    " : " ++| (ribbonEmpty \\\ [
                  fine2pretty (ctx2scCtx gamma) ddom opts,
                  ribbon " => ",
                  fine2pretty (ctx2scCtx gamma) dcod opts])
    ]
jud2pretty (JudModedModalityRel modrel gamma (ModedModality ddom1 mu1) (ModedModality ddom2 mu2) dcod) opts =
  ctx2pretty gamma opts \\\ [
    _vdash ++ " <mode;modty> " ++| (ribbonEmpty \\\ [
                  fine2pretty (ctx2scCtx gamma) mu1 opts,
                  ribbon modrelsign,
                  fine2pretty (ctx2scCtx gamma) mu2 opts]),
    " : " ++| (ribbonEmpty \\\ [
                  "(" ++| fine2pretty (ctx2scCtx gamma) ddom1 opts,
                  ribbon " = ",
                  fine2pretty (ctx2scCtx gamma) ddom2 opts |++ ")",
                  ribbon " => ",
                  fine2pretty (ctx2scCtx gamma) dcod opts])
    ]
  where modrelsign = case modrel of
          ModEq -> " = "
          ModLeq -> " =< "
jud2pretty (JudSegment gamma seg) opts = ctx2pretty gamma opts \\\ [_vdash ++ " <segment> " ++| fine2pretty (ctx2scCtx gamma) seg opts]
jud2pretty (JudVal gamma val) opts = ctx2pretty gamma opts \\\ [_vdash ++ " <val> " ++| fine2pretty (ctx2scCtx gamma) val opts]
jud2pretty (JudModule gamma modul) opts = ctx2pretty gamma opts \\\ [_vdash ++ " <module> " ++| fine2pretty (ctx2scCtx gamma) modul opts]
jud2pretty (JudEntry gamma entry) opts = ctx2pretty gamma opts \\\ [_vdash ++ " <declaration> " ++| fine2pretty (ctx2scCtx gamma) entry opts]
--jud2pretty jud = _jud2pretty

jud2string :: forall sys .
  (Multimode sys,
   SysPretty sys) =>
  Judgement sys -> Fine2PrettyOptions sys -> String
jud2string jud opts = render (jud2pretty jud opts) (_fine2pretty'renderOptions opts)

instance (Multimode sys,
          SysPretty sys)
         => Show (Judgement sys) where
  show jud = render (jud2pretty jud $? id) $? id
-}
