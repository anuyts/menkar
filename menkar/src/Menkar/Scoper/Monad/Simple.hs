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
import Menkar.Systems.Trivial.Fine

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
  annot4annot gamma qstring maybeArg = case (qstring, maybeArg) of
    (Raw.Qualified [] "~", Nothing) -> return AnnotImplicit
    _ -> scopeFail $ "Illegal annotation: " ++ (render
             (Raw.unparse' qstring \\\ (maybeToList $ ($? id) . fine2pretty (ctx2scCtx gamma) <$> maybeArg))
             $? id
           )
  newMetaTermNoCheck maybeParent deg gamma etaFlag reason = do
    i <- fresh
    return $ Expr2 $ TermMeta etaFlag i $ Compose $ Var2 <$> scListVariables (ctx2scCtx gamma)
  newMetaMode maybeParent gamma reason = return U1
  newMetaModty maybeParent gamma reason = return U1
  scopeFail msg = SimpleScoper $ lift $ Left msg

---------------------------

testscope :: String -> IO (Either _ (Either String (Entry Trivial Void)))
testscope filename = do
  errorOrRawFile <- P.testparse filename
  return $ evalSimpleScoper . file (CtxEmpty U1) <$> errorOrRawFile
