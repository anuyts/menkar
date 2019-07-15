module Menkar.Systems.Reldtt.TC where

import Menkar.Basic
import Menkar.Analyzer
import Menkar.WHN
import Menkar.TC
import Menkar.System.Fine
import Menkar.System.Scoper
import Menkar.System.WHN
import Menkar.System.TC
import Menkar.Fine
import Menkar.Monad
import Menkar.Systems.Reldtt.Fine
import Menkar.Systems.Reldtt.Analyzer
import Menkar.Systems.Reldtt.Scoper
import Menkar.Systems.Reldtt.WHN

import Control.Monad.DoUntilFail
import Control.Exception.AssertFalse
import Data.Functor.Coerce

import Control.Monad.Trans.Class
import Control.Monad.Writer.Class
import Control.Monad.Trans.Writer.Lazy
import Control.Monad.Trans.Maybe
import Control.Monad.State.Lazy
import Control.Applicative
import Control.Lens
import Data.Void
import GHC.Generics
import Data.Functor.Compose
import Data.Maybe
import Data.List.Ordered

instance SysTC Reldtt where

  checkSysJudgement jud = case jud of {}

  checkSysASTUnanalyzable sysError gamma (t :: t v) extraT maybeCT = case (sysError, analyzableToken @Reldtt @t, t) of
    (AnErrorModtySnout, AnTokenSys AnTokenModtySnout, Const (ModtySnout idom icod krevdegs)) -> do
      when (not (isSortedBy (>=) krevdegs)) $
        tcFail "Degrees are not ordered."
      when (any (\ kdeg -> (kdeg >= KnownDeg idom) && (kdeg < KnownDegOmega)) krevdegs) $
        tcFail "A degree is unavailable in the domain."
      when (any (== KnownDegProblem) krevdegs) $ tcFail "Problematic degree encountered."
      return U1
    (AnErrorModtySnout, _, _) -> unreachable
