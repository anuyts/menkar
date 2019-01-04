module Control.Exception.AssertFalse where

--import Control.Exception (assert)
import Debug.Trace
import GHC.Stack

assertFalse :: HasCallStack => String -> a
assertFalse msg = traceStack msg (error msg)
--assertFalse msg = assert False (error msg)

todo :: HasCallStack => a
todo = assertFalse "Todo."

unreachable :: HasCallStack => a
unreachable = assertFalse "Unreachable."

-- :set -fbreak-on-error
