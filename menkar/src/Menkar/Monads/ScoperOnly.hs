{-# LANGUAGE NoDeriveAnyClass, GeneralizedNewtypeDeriving #-}

module Menkar.Monads.ScoperOnly where

import Menkar.Monad.Monad
import Menkar.Fine.Syntax
--import Menkar.Fine.Judgement
import Menkar.Basic.Context
import Menkar.PrettyPrint.Aux.Context
import Menkar.Fine.Context
import Menkar.System.Fine
import Menkar.PrettyPrint.Fine
import qualified Menkar.Raw as Raw
import qualified Menkar.PrettyPrint.Raw as Raw
import Menkar.Systems.Trivial.Trivial

import Control.Exception.AssertFalse
import Data.Omissible

import Control.Monad.State.Lazy
import Control.Monad.Fail
import GHC.Generics (U1 (..))
import Text.PrettyPrint.Tree
import Data.Functor.Compose
import Data.Void
import Data.Maybe

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

instance MonadFail SimpleScoper where
  fail s = unreachable

instance MonadScoper Trivial SimpleScoper where
  newMetaTermNoCheck maybeParent gamma etaFlag maybeAlg reason = do
    i <- fresh
    return $ Expr2 $ TermMeta etaFlag i (Compose $ Var2 <$> scListVariables (ctx2scCtx gamma)) (Compose maybeAlg)
  scopeFail msg = SimpleScoper $ lift $ Left msg

---------------------------

testscope :: String -> IO (Either _ (Either String (Entry Trivial Void)))
testscope filename = do
  errorOrRawFile <- P.testparse filename
  return $ evalSimpleScoper . file (CtxEmpty U1) <$> errorOrRawFile
