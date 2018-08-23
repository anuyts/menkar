module Control.Exception.AssertFalse where

import Control.Exception (assert)

assertFalse :: String -> a
assertFalse msg = assert False (error msg)

todo :: a
todo = assertFalse "Todo."

unreachable :: a
unreachable = assertFalse "Unreachable."
