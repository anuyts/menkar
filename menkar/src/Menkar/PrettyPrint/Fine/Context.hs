{-# LANGUAGE UndecidableInstances #-}

module Menkar.PrettyPrint.Fine.Context where

import Menkar.Fine.Syntax
import Menkar.Basic.Context
import Menkar.Fine.Context
import Menkar.Fine.Multimode
import Menkar.PrettyPrint.Aux.Context
import qualified Menkar.Raw as Raw
import qualified Menkar.PrettyPrint.Raw as Raw
import Menkar.PrettyPrint.Fine.Syntax

import Text.PrettyPrint.Tree
import Data.Omissible

import Data.Void
import Data.Maybe
import Data.Proxy
import Control.Exception.AssertFalse
import Data.Functor.Compose
import Data.Functor.Const
import Control.Lens

{-| Prettyprint a context, while left dividing all variables' modalities with the given one,
    if present. This function ignores the option @'_fine2pretty'explicitLeftDivision'@.
    The printed context is presumed to have no references to its own variables.
-}
dividedCtx2pretty :: forall v w sys ty .
  (DeBruijnLevel v,
   Multimode sys, Functor (ty sys),
   Fine2Pretty sys (Mode sys), Fine2Pretty sys (Modality sys), Fine2Pretty sys (ty sys)) =>
  Maybe (ModedModality sys v) -> ScCtx sys v Void -> Ctx ty sys w v -> Fine2PrettyOptions sys -> PrettyTree String
dividedCtx2pretty maybeDRho delta (CtxEmpty d) opts = "{context-mode : " ++| fine2pretty delta d opts |++ "}"
dividedCtx2pretty maybeDRho delta (gamma :.. seg) opts = --haveDB gamma $
  dividedCtx2pretty maybeDRho delta gamma opts
    \+\ [seg2pretty (maybeDRho) delta (unVarBeforeCtxUnsafe <$> seg) opts]
dividedCtx2pretty maybeDRho delta (seg :^^ gamma) opts = todo
dividedCtx2pretty maybeDRho delta (gamma :<...> modul) opts = --haveDB gamma $
  dividedCtx2pretty maybeDRho delta gamma opts
dividedCtx2pretty Nothing delta (dmu :\\ gamma) opts = --haveDB gamma $
  "[" ++| fine2pretty delta (unVarBeforeCtxUnsafe <$> dmu) opts |++ "] \\ ("
                             \\\ [dividedCtx2pretty Nothing delta gamma opts]
                             /// ribbon ")"
dividedCtx2pretty (Just drho) delta (dmu :\\ gamma) opts =
  dividedCtx2pretty (Just $ compModedModality (unVarBeforeCtxUnsafe <$> dmu) drho) delta gamma opts

ctx2pretty :: forall v sys ty .
  (DeBruijnLevel v,
   Multimode sys, Functor (ty sys),
   Fine2Pretty sys (Mode sys), Fine2Pretty sys (Modality sys), Fine2Pretty sys (ty sys)) =>
  Ctx ty sys v Void -> Fine2PrettyOptions sys -> PrettyTree String
ctx2pretty gamma opts = dividedCtx2pretty maybeDRho (ctx2scCtx gamma) (externalizeCtx gamma) opts
  where maybeDRho = if _fine2pretty'explicitLeftDivision opts
          then Nothing
          else Just $ idModedModality $ unVarFromCtx <$> ctx'mode gamma

ctx2string :: forall v sys ty .
  (DeBruijnLevel v,
   Multimode sys, Functor (ty sys),
   Fine2Pretty sys (Mode sys), Fine2Pretty sys (Modality sys), Fine2Pretty sys (ty sys)) =>
  Ctx ty sys v Void -> Fine2PrettyOptions sys -> String
ctx2string gamma opts = render (ctx2pretty gamma opts) (_fine2pretty'renderOptions opts)

instance
  (DeBruijnLevel v,
   Multimode sys, Functor (ty sys),
   Fine2Pretty sys (Mode sys), Fine2Pretty sys (Modality sys), Fine2Pretty sys (ty sys)) =>
  Show (Ctx ty sys v Void) where
  show gamma = ctx2string gamma omit

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
