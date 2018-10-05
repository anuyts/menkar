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

{-
type SimpleScoper = StateT Int (Either String)
fresh :: MonadState Int m => m Int
fresh = state $ \ i -> (i, i+1)
-}

newtype SimpleScoper a = SimpleScoper (StateT Int (Either String) a)
  deriving (Functor, Applicative, Monad, MonadState Int)

fresh :: MonadState Int m => m Int
fresh = state $ \ i -> (i, i+1)

instance Fine2Pretty U1 U1 Mode where
  fine2pretty gamma (Mode U1) = ribbon "*"
instance Fine2Pretty U1 U1 Modty where
  fine2pretty gamma (Modty U1) = ribbon "*->*"

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
