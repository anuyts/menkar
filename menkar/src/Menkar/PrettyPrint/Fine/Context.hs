{-# LANGUAGE UndecidableInstances #-}

module Menkar.PrettyPrint.Fine.Context where

import Menkar.Fine.Syntax
import Menkar.Basic.Context
import Menkar.Fine.Context
import Menkar.System.Fine
import Menkar.PrettyPrint.Aux.Context
import qualified Menkar.Raw as Raw
import qualified Menkar.PrettyPrint.Raw as Raw
import Menkar.PrettyPrint.Fine.Class
import Menkar.PrettyPrint.Fine.Syntax
import Menkar.System.PrettyPrint

import Text.PrettyPrint.Tree
import Data.Omissible

import Data.Void
import Data.Maybe
import Control.Exception.AssertFalse
import Data.Functor.Compose
import Data.Functor.Const
import Control.Lens

{-| Prettyprint a context. This function ignores the option @'_fine2pretty'explicitLeftDivision'@.
-}
ctx2pretty :: forall v sys ty .
  (DeBruijnLevel v,
   Multimode sys, Functor (ty sys),
   SysFinePretty sys, Fine2Pretty sys (ty sys)) =>
  Ctx ty sys v -> Fine2PrettyOptions sys -> PrettyTree String
ctx2pretty (CtxEmpty d) opts =
  "{context-mode : " ++| fine2pretty (ScCtxEmpty) d opts |++ "}"
ctx2pretty ((gamma :: Ctx ty sys w) :.. seg) opts = haveDB gamma $
  ctx2pretty gamma opts
    \+\ [
      seg2pretty (ctx2scCtx gamma) seg (size @w) opts
    ]
ctx2pretty (gamma :<...> modul) opts = haveDB gamma $
  case _fine2pretty'printModuleInContext opts of
    Nothing -> ctx2pretty gamma opts
    Just p -> ctx2pretty gamma opts
      \+\ [
        let printModule = moduleContents2pretty (ctx2scCtx gamma) (modul)
                            $ opts & fine2pretty'printModule .~ p
        in ribbon "{" \\\ printModule /// ribbon "}"
      ]
ctx2pretty (dmu :\\ gamma) opts = haveDB gamma $
  ctx2pretty gamma opts \+\ [
      " {" ++| fine2pretty (ctx2scCtx gamma) (dmu) opts |++ "}"
    ]
--  "[" ++| fine2pretty delta (unVarBeforeCtxUnsafe <$> dmu) opts |++ "] \\ ("
--                             \\\ [ctx2pretty Nothing delta gamma opts]
--                             /// ribbon ")"
ctx2pretty (CtxId gamma) opts = haveDB gamma $ ctx2pretty gamma opts
ctx2pretty (CtxComp gamma) opts = haveDB gamma $ ctx2pretty gamma opts
ctx2pretty (CtxOpaque d) opts = unreachable

ctx2string :: forall v sys ty .
  (DeBruijnLevel v,
   Multimode sys, Functor (ty sys),
   SysFinePretty sys, Fine2Pretty sys (ty sys)) =>
  Ctx ty sys v -> Fine2PrettyOptions sys -> String
ctx2string gamma opts = render (ctx2pretty gamma opts) (_fine2pretty'renderOptions opts)

instance
  (DeBruijnLevel v,
   Multimode sys, Functor (ty sys),
   SysFinePretty sys, Fine2Pretty sys (ty sys)) =>
  Show (Ctx ty sys v) where
  show gamma = ctx2string gamma omit

{-
ctx2pretties :: forall v sys ty .
  (DeBruijnLevel v,
   SysTrav sys, Functor (ty sys),
   Fine2Pretty sys (Mode sys), Fine2Pretty sys Modty, Fine2Pretty sys ty) =>
  Ctx ty sys v -> [PrettyTree String]
ctx2pretties (CtxEmpty d) = ["{[" ++| fine2pretty ScCtxEmpty (Mode d :: Mode sys Void) |++ "]}"]
ctx2pretties (gamma :.. seg) = haveDB gamma $ ctx2pretties gamma ++ [fine2pretty (ctx2scCtx gamma) (unVarFromCtx <$> seg)]
ctx2pretties (seg :^^ gamma) = todo
ctx2pretties (gamma :<...> modul) = haveDB gamma $ ctx2pretties gamma
ctx2pretties (dmu :\\ gamma) = haveDB gamma $ [fine2pretty (ctx2scCtx gamma) (unVarFromCtx <$> dmu) |++ "\\ ("
                             \\\ ctx2pretties gamma
                             /// ribbon ")"]

ctx2pretty :: forall v sys ty .
  (DeBruijnLevel v,
   SysTrav sys, Functor (ty sys),
   Fine2Pretty sys (Mode sys), Fine2Pretty sys Modty, Fine2Pretty sys ty) =>
  Ctx ty sys v -> PrettyTree String
ctx2pretty (CtxEmpty d) = "{[" ++| fine2pretty ScCtxEmpty (Mode d :: Mode sys Void) |++ "]}"
ctx2pretty (gamma :.. seg) = haveDB gamma $ ctx2pretty gamma ||| fine2pretty (ctx2scCtx gamma) (unVarFromCtx <$> seg)
ctx2pretty (seg :^^ gamma) = todo
ctx2pretty (gamma :<...> modul) = haveDB gamma $ ctx2pretty gamma
ctx2pretty (dmu :\\ gamma) = haveDB gamma $ fine2pretty (ctx2scCtx gamma) (unVarFromCtx <$> dmu) |++ "\\ ("
                             \\\ [ctx2pretty gamma]
                             /// ribbon ")"
-}
