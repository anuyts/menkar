module Control.Exception.AssertFalse where

--import Control.Exception (assert)
import Debug.Trace
import GHC.Stack
import Control.Lens
import Data.Maybe

assertFalse :: HasCallStack => String -> a
assertFalse msg = traceStack msg (error msg)
--assertFalse msg = assert False (error msg)

todo :: HasCallStack => a
todo = assertFalse "Todo."

unreachable :: HasCallStack => a
unreachable = assertFalse "Unreachable."

_JustUnsafe :: HasCallStack => Lens (Maybe a) (Maybe b) a b
_JustUnsafe f Nothing = unreachable
_JustUnsafe f (Just a) = Just <$> f a

_LeftUnsafe :: HasCallStack => Lens (Either a s) (Either b t) a b
_LeftUnsafe f (Right _) = unreachable
_LeftUnsafe f (Left a) = Left <$> f a

_RightUnsafe :: HasCallStack => Lens (Either s a) (Either t b) a b
_RightUnsafe f (Left _) = unreachable
_RightUnsafe f (Right a) = Right <$> f a

-- :set -fbreak-on-error
