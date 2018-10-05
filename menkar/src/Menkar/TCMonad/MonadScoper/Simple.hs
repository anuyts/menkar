{-# LANGUAGE NoDeriveAnyClass, GeneralizedNewtypeDeriving #-}

module Menkar.TCMonad.MonadScoper.Simple where

import Menkar.TCMonad.MonadScoper
import Menkar.Fine.Syntax
import Menkar.Fine.Judgement
import Menkar.Fine.Context.Variable
import Menkar.Fine.Context
import Menkar.Fine.Substitution
import Menkar.Fine.PrettyPrint
import qualified Menkar.Raw as Raw
import Control.Monad.State.Lazy
import GHC.Generics (U1 (..))
import Text.PrettyPrint.Tree
import Data.Functor.Compose
import Data.Void

import qualified Menkar.Parser as P -- for testscope
import Menkar.Scoper -- for testscope

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

instance Fine2Pretty U1 U1 Mode where
  fine2pretty gamma (Mode U1) = ribbon "data"
instance Fine2Pretty U1 U1 Modty where
  fine2pretty gamma (Modty U1) = ribbon "map"

instance MonadScoper U1 U1 U1 SimpleScoper where
  annot4annot gamma qstring args = case (qstring, args) of
    (Raw.Qualified [] "~", []) -> return AnnotImplicit
    _ -> scopeFail $ "Illegal annotation: " ++ (render defaultRenderState $
             Raw.unparse' qstring \\\ fine2pretty gamma <$> args
           )
  term4newImplicit gamma = do
    i <- fresh
    return $ Expr3 $ TermMeta i $ Compose $ Var3 <$> scListVariables gamma
  mode4newImplicit gamma = return U1
  modty4newImplicit gamma = return U1
  scopeFail msg = SimpleScoper $ lift $ Left msg

---------------------------

testscope :: String -> IO (Either _ (Either String (Entry U1 U1 Void)))
testscope filename = do
  errorOrRawFile <- P.testparse filename
  return $ case errorOrRawFile of
    Left error -> Left $ error
    Right rawFile -> Right $ evalSimpleScoper $ file ScCtxEmpty rawFile
