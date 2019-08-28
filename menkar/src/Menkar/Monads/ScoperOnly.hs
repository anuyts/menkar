{-# LANGUAGE NoDeriveAnyClass, GeneralizedNewtypeDeriving #-}

module Menkar.Monads.ScoperOnly where

import Menkar.Monad.Monad
import Menkar.Fine.Syntax
import Menkar.Fine.LookupQName
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

import Control.Monad.State.Strict
import Control.Monad.Fail
import Control.Lens
import GHC.Generics (U1 (..))
import Text.PrettyPrint.Tree
import Data.Functor.Compose
import Data.Void
import Data.Maybe
import GHC.Generics

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
  newMetaID gamma reason = do
    i <- fresh
    return (i, Dependencies $ liftFS $ Compose $ forallVarsRev $ \ (v :: v) ->
        let d :: TrivMode v
            d = _modalityTo'dom $ _segment'modty $ _leftDivided'content $ uncoy $ lookupVar gamma v
        in  d :*: Var2 v
      )
  scopeFail msg = SimpleScoper $ lift $ Left msg

---------------------------

testscope :: String -> IO (Either _ (Either String (Entry Trivial Void)))
testscope filename = do
  errorOrRawFile <- P.testparse filename
  return $ evalSimpleScoper . file (CtxEmpty TrivMode) <$> errorOrRawFile
