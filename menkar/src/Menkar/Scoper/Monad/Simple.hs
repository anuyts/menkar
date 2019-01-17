{-# LANGUAGE NoDeriveAnyClass, GeneralizedNewtypeDeriving #-}

module Menkar.Scoper.Monad.Simple where

import Menkar.TC.Monad
import Menkar.Fine.Syntax
--import Menkar.Fine.Judgement
import Menkar.Basic.Context
import Menkar.PrettyPrint.Aux.Context
import Menkar.Fine.Context
import Menkar.Fine.Multimode
import Menkar.PrettyPrint.Fine
import qualified Menkar.Raw as Raw
import qualified Menkar.PrettyPrint.Raw as Raw
import Menkar.Fine.Multimode.Trivial

import Control.Monad.State.Lazy
import GHC.Generics (U1 (..))
import Text.PrettyPrint.Tree
import Data.Functor.Compose
import Data.Void

import qualified Menkar.Parser as P -- for testscope
import Menkar.Scoper.Scoper -- for testscope

{-
type SimpleScoper = StateT Int (Either String)
fresh :: MonadState Int m => m Int
fresh = state $ \ i -> (i, i+1)
-}

newtype SimpleScoper a = SimpleScoper (StateT Int (Either String) a)
  deriving (Functor, Applicative, Monad, MonadState Int)

evalSimpleScoper :: SimpleScoper a -> Either String a
evalSimpleScoper (SimpleScoper prog) = evalStateT prog 0

fresh :: MonadState Int m => m Int
fresh = state $ \ i -> (i, i+1)

instance MonadScoper U1 U1 U1 SimpleScoper where
  annot4annot gamma qstring args = case (qstring, args) of
    (Raw.Qualified [] "~", []) -> return AnnotImplicit
    _ -> scopeFail $ "Illegal annotation: " ++ (render defaultRenderState $
             Raw.unparse' qstring \\\ fine2pretty (ctx2scCtx gamma) <$> args
           )
  newMetaTermNoCheck maybeParent deg gamma etaFlag reason = do
    i <- fresh
    return $ Expr3 $ TermMeta etaFlag i $ Compose $ Var3 <$> scListVariables (ctx2scCtx gamma)
  newMetaMode maybeParent gamma reason = return U1
  newMetaModty maybeParent gamma reason = return U1
  scopeFail msg = SimpleScoper $ lift $ Left msg

---------------------------

testscope :: String -> IO (Either _ (Either String (Entry U1 U1 Void)))
testscope filename = do
  errorOrRawFile <- P.testparse filename
  return $ evalSimpleScoper . file (CtxEmpty U1) <$> errorOrRawFile
