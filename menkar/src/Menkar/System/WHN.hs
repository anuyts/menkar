module Menkar.System.WHN where

import Menkar.System.Fine
import Menkar.System.Scoper
import Menkar.Fine
import Menkar.Monad.Monad

import Data.Void
import Control.Monad.Writer

class SysScoper sys => SysWHN sys where
  whnormalizeSys :: MonadWHN sys whn =>
    Constraint sys ->
    Ctx Type sys v Void ->
    SysTerm sys v ->
    String ->
    WriterT [Int] whn (Term sys v)
  {-| @'leqMod' ddom dcod mu1 mu2@ returns whether @mu1 <= mu2@, or
      @'Nothing'@ if it is presently unclear.
      This method may call @'awaitMeta'@.
  -}
  leqMod :: forall whn v .
    (MonadWHN sys whn, DeBruijnLevel v) =>
    Mode sys v -> Mode sys v -> Modality sys v -> Modality sys v -> whn (Maybe Bool)
  {-| @'leqDeg' d deg1 deg2@ returns whether @deg1 <= deg2@ (equality is the least), or
      @'Nothing'@ if it is presently unclear but may become clear.
      This method may call @'awaitMeta'@.
  -}
  leqDeg :: forall whn v .
    (MonadWHN sys whn, DeBruijnLevel v) =>
    Mode sys v -> Degree sys v -> Degree sys v -> whn (Maybe Bool)
    
  isEqDeg :: forall whn v .
    (MonadWHN sys whn, DeBruijnLevel v) =>
    Mode sys v -> Degree sys v -> whn (Maybe Bool)
  isEqDeg d deg = leqDeg d deg eqDeg

  isTopDeg :: forall whn v .
    (MonadWHN sys whn, DeBruijnLevel v) =>
    Mode sys v -> Degree sys v -> whn (Maybe Bool)
  isTopDeg d deg = case maybeTopDeg of
    Nothing -> return $ Just False
    Just topDeg -> leqDeg d topDeg deg
