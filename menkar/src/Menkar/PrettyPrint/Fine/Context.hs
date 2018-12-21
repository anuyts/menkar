module Menkar.PrettyPrint.Fine.Context where

import Menkar.Fine.Syntax
import Menkar.Basic.Context
import Menkar.Fine.Context
import Menkar.PrettyPrint.Aux.Context
import qualified Menkar.Raw as Raw
import qualified Menkar.PrettyPrint.Raw as Raw
import Text.PrettyPrint.Tree
import Menkar.PrettyPrint.Fine.Syntax

import Data.Void
import Data.Maybe
import Data.Proxy
import Control.Exception.AssertFalse
import Data.Functor.Compose
import Data.Functor.Const
import Control.Lens

ctx2pretty :: forall v mode modty ty .
  (DeBruijnLevel v,
   Functor mode, Functor modty, Functor (ty mode modty),
   Fine2Pretty mode modty Mode, Fine2Pretty mode modty Modty, Fine2Pretty mode modty ty) =>
  Ctx ty mode modty v Void -> PrettyTree String
ctx2pretty (CtxEmpty d) = "{[" ++| fine2pretty ScCtxEmpty (Mode d :: Mode mode modty Void) |++ "]}"
ctx2pretty (gamma :.. seg) = haveDB gamma $ ctx2pretty gamma \+\ [fine2pretty (ctx2scCtx gamma) (unVarFromCtx <$> seg)]
ctx2pretty (seg :^^ gamma) = todo
ctx2pretty (gamma :<...> modul) = haveDB gamma $ ctx2pretty gamma
ctx2pretty (dmu :\\ gamma) = haveDB gamma $ fine2pretty (ctx2scCtx gamma) (unVarFromCtx <$> dmu) |++ "\\ ("
                             \\\ [ctx2pretty gamma]
                             /// ribbon ")"

{-
ctx2pretties :: forall v mode modty ty .
  (DeBruijnLevel v,
   Functor mode, Functor modty, Functor (ty mode modty),
   Fine2Pretty mode modty Mode, Fine2Pretty mode modty Modty, Fine2Pretty mode modty ty) =>
  Ctx ty mode modty v Void -> [PrettyTree String]
ctx2pretties (CtxEmpty d) = ["{[" ++| fine2pretty ScCtxEmpty (Mode d :: Mode mode modty Void) |++ "]}"]
ctx2pretties (gamma :.. seg) = haveDB gamma $ ctx2pretties gamma ++ [fine2pretty (ctx2scCtx gamma) (unVarFromCtx <$> seg)]
ctx2pretties (seg :^^ gamma) = todo
ctx2pretties (gamma :<...> modul) = haveDB gamma $ ctx2pretties gamma
ctx2pretties (dmu :\\ gamma) = haveDB gamma $ [fine2pretty (ctx2scCtx gamma) (unVarFromCtx <$> dmu) |++ "\\ ("
                             \\\ ctx2pretties gamma
                             /// ribbon ")"]

ctx2pretty :: forall v mode modty ty .
  (DeBruijnLevel v,
   Functor mode, Functor modty, Functor (ty mode modty),
   Fine2Pretty mode modty Mode, Fine2Pretty mode modty Modty, Fine2Pretty mode modty ty) =>
  Ctx ty mode modty v Void -> PrettyTree String
ctx2pretty (CtxEmpty d) = "{[" ++| fine2pretty ScCtxEmpty (Mode d :: Mode mode modty Void) |++ "]}"
ctx2pretty (gamma :.. seg) = haveDB gamma $ ctx2pretty gamma ||| fine2pretty (ctx2scCtx gamma) (unVarFromCtx <$> seg)
ctx2pretty (seg :^^ gamma) = todo
ctx2pretty (gamma :<...> modul) = haveDB gamma $ ctx2pretty gamma
ctx2pretty (dmu :\\ gamma) = haveDB gamma $ fine2pretty (ctx2scCtx gamma) (unVarFromCtx <$> dmu) |++ "\\ ("
                             \\\ [ctx2pretty gamma]
                             /// ribbon ")"
-}
