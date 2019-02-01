{-# LANGUAGE UndecidableInstances #-}

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

ctx2pretty :: forall v sys ty .
  (DeBruijnLevel v,
   SysTrav sys, Functor (ty sys),
   Fine2Pretty sys (Mode sys), Fine2Pretty sys (Modality sys), Fine2Pretty sys (ty sys)) =>
  Ctx ty sys v Void -> PrettyTree String
ctx2pretty (CtxEmpty d) = "{context-mode : " ++| fine2pretty ScCtxEmpty d |++ "}"
ctx2pretty (gamma :.. seg) = haveDB gamma $ ctx2pretty gamma \+\ [fine2pretty (ctx2scCtx gamma) (unVarFromCtx <$> seg)]
ctx2pretty (seg :^^ gamma) = todo
ctx2pretty (gamma :<...> modul) = haveDB gamma $ ctx2pretty gamma
ctx2pretty (dmu :\\ gamma) = haveDB gamma $ "[" ++| fine2pretty (ctx2scCtx gamma) (unVarFromCtx <$> dmu) |++ "] \\ ("
                             \\\ [ctx2pretty gamma]
                             /// ribbon ")"

ctx2string :: forall v sys ty .
  (DeBruijnLevel v,
   SysTrav sys, Functor (ty sys),
   Fine2Pretty sys (Mode sys), Fine2Pretty sys (Modality sys), Fine2Pretty sys (ty sys)) =>
  Ctx ty sys v Void -> String
ctx2string gamma = render defaultRenderState $ ctx2pretty gamma

instance
  (DeBruijnLevel v,
   SysTrav sys, Functor (ty sys),
   Fine2Pretty sys (Mode sys), Fine2Pretty sys (Modality sys), Fine2Pretty sys (ty sys)) =>
  Show (Ctx ty sys v Void) where
  show = ctx2string

{-
ctx2pretties :: forall v sys ty .
  (DeBruijnLevel v,
   SysTrav sys, Functor (ty sys),
   Fine2Pretty sys (Mode sys), Fine2Pretty sys Modty, Fine2Pretty sys ty) =>
  Ctx ty sys v Void -> [PrettyTree String]
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
  Ctx ty sys v Void -> PrettyTree String
ctx2pretty (CtxEmpty d) = "{[" ++| fine2pretty ScCtxEmpty (Mode d :: Mode sys Void) |++ "]}"
ctx2pretty (gamma :.. seg) = haveDB gamma $ ctx2pretty gamma ||| fine2pretty (ctx2scCtx gamma) (unVarFromCtx <$> seg)
ctx2pretty (seg :^^ gamma) = todo
ctx2pretty (gamma :<...> modul) = haveDB gamma $ ctx2pretty gamma
ctx2pretty (dmu :\\ gamma) = haveDB gamma $ fine2pretty (ctx2scCtx gamma) (unVarFromCtx <$> dmu) |++ "\\ ("
                             \\\ [ctx2pretty gamma]
                             /// ribbon ")"
-}
