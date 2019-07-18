module Menkar.Systems.Reldtt.Raw where

import Menkar.Systems.Reldtt.Basic
import Menkar.Raw

type instance SysExprC Reldtt = KnownModty

data KnownModty = KnownModty {_knownModty'snout :: ModtySnout, _knownModty'tail :: ModtyTail}

newtype ModtyTail = ModtyTail {_modtyTail'aspects :: [ModtyTailAspect]}
data ModtyTailAspect = ModtyTailAspect String (ExprC Reldtt)
