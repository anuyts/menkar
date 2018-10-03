module Menkar.TCMonad.MonadScoper.Simple where

import Menkar.TCMonad.MonadScoper
import Menkar.Fine.Syntax
import Menkar.Fine.Judgement
import Menkar.Fine.Context.Variable
import Menkar.Fine.Context
import Menkar.Fine.Substitution
import qualified Menkar.Raw.Syntax as Raw
import Control.Monad.State.Lazy
import GHC.Generics (U1 (..))

type SimpleScoper = StateT Int (Either String)
fresh :: MonadState Int m => m Int
fresh = state $ \ i -> (i, i+1)

instance MonadScoper U1 U1 U1 SimpleScoper where
  term4qname = _
  annot4annot = _
  term4newImplicit gamma = do
    i <- fresh
    return $ Expr3 $ TermMeta i _listAllVariables
  mode4newImplicit gamma = return U1
  modty4newImplicit gamma = return U1
  scopeFail msg = lift $ Left msg
