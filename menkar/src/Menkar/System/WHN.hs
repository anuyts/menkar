module Menkar.System.WHN where

import Menkar.System.Fine
import Menkar.Fine
import Menkar.Monad.Monad

import Data.Void
import Control.Monad.Writer

class SysSyntax (Term sys) sys => SysWHN sys where
  whnormalizeSys :: MonadTC sys tc =>
    Constraint sys ->
    Ctx Type sys v Void ->
    SysTerm sys v ->
    String ->
    WriterT [Int] tc (Term sys v)
  {-| @'leqMod' ddom dcod mu1 mu2@ returns whether @mu1 <= mu2@, or
      @'Nothing'@ if it is presently unclear.
      This method may call @'awaitMeta'@.
  -}
  leqMod :: forall tc v .
    (MonadTC sys tc, DeBruijnLevel v) =>
    Mode sys v -> Mode sys v -> Modality sys v -> Modality sys v -> tc (Maybe Bool)
  {-| @'leqDeg' d deg1 deg2@ returns whether @deg1 <= deg2@ (equality is the least), or
      @'Nothing'@ if it is presently unclear but may become clear.
      This method may call @'awaitMeta'@.
  -}
  leqDeg :: forall tc v .
    (MonadTC sys tc, DeBruijnLevel v) =>
    Mode sys v -> Degree sys v -> Degree sys v -> tc (Maybe Bool)
    
  isEqDeg :: forall tc v .
    (MonadTC sys tc, DeBruijnLevel v) =>
    Mode sys v -> Degree sys v -> tc (Maybe Bool)
  isEqDeg d deg = leqDeg d deg eqDeg
