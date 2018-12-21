module Menkar.PrettyPrint.Fine.Judgement where

import Menkar.Fine.Syntax
import Menkar.Basic.Context
import Menkar.Fine.Context
import Menkar.PrettyPrint.Aux.Context
import qualified Menkar.Raw as Raw
import qualified Menkar.PrettyPrint.Raw as Raw
import Text.PrettyPrint.Tree
import Menkar.PrettyPrint.Fine.Syntax
import Menkar.PrettyPrint.Fine.Context

import Data.Void
import Data.Maybe
import Data.Proxy
import Control.Exception.AssertFalse
import Data.Functor.Compose
import Data.Functor.Const
import Control.Lens
