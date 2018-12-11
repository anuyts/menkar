module Menkar.TC.Monad.TCDTT where

import Control.Monad.Cont
import Control.Monad.State.Lazy
import Control.Monad.List
import Control.Monad.Except

data TCResult = TCSuccess | TCWaiting

data TCState = TCState
  { }

data TCError =
  TCErrorConstraintBound |
  TCErrorBlocked |
  TCErrorTCFail |
  TCErrorScopeFail

newtype TCT m a = TCT {unTCT :: ContT TCResult (StateT TCState ({-ListT-} (ExceptT TCError m))) a}

runTCT :: (Monad m) => TCT m () -> TCState -> ExceptT TCError m (TCResult, TCState)
runTCT program initState = flip runStateT initState $ runContT (unTCT program) (\() -> return TCSuccess)

