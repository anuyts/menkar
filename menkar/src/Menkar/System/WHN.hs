module Menkar.System.WHN where

import Menkar.System.Fine
import Menkar.System.Scoper
import Menkar.Fine
import Menkar.Monad.Monad

import Data.Void
import Control.Monad.Writer

class SysScoper sys => SysWHN sys where
  whnormalizeSys :: forall whn v .
    (MonadWHN sys whn, MonadWriter [Int] whn, DeBruijnLevel v) =>
    Constraint sys ->
    Ctx Type sys v Void ->
    SysTerm sys v ->
    Type sys v ->
    String ->
    whn (Term sys v)
  {-| @'leqMod' ddom dcod mu1 mu2@ returns whether @mu1 <= mu2@, or
      @'Nothing'@ if it is presently unclear.
      This method may call @'awaitMeta'@.
      This method should be efficient and can be ridiculously strict; the relation should probably be transitive,
      but reflexivity is not even required. It should imply validity of the inequality judgement.
  -}
  leqMod :: forall whn v .
    (MonadWHN sys whn, DeBruijnLevel v) =>
    Constraint sys ->
    Ctx Type sys v Void ->
    Modality sys v -> Modality sys v ->
    Mode sys v -> Mode sys v ->
    String ->
    whn (Maybe Bool)
  {-| @'leqDeg' d deg1 deg2@ returns whether @deg1 <= deg2@ (the equality-degree is the least), or
      @'Nothing'@ if it is presently unclear but may become clear.
      This method may call @'awaitMeta'@.
  -}
  leqDeg :: forall whn v .
    (MonadWHN sys whn, DeBruijnLevel v) =>
    Constraint sys ->
    Ctx Type sys v Void ->
    Degree sys v -> 
    Degree sys v -> 
    Mode sys v ->
    String ->
    whn (Maybe Bool)
    
  isEqDeg :: forall whn v .
    (MonadWHN sys whn, DeBruijnLevel v) =>
    Constraint sys ->
    Ctx Type sys v Void ->
    Degree sys v -> 
    Mode sys v ->
    String ->
    whn (Maybe Bool)
  isEqDeg parent gamma deg d reason = leqDeg parent gamma deg eqDeg d reason

  isTopDeg :: forall whn v .
    (MonadWHN sys whn, DeBruijnLevel v) =>
    Constraint sys ->
    Ctx Type sys v Void ->
    Degree sys v -> 
    Mode sys v ->
    String ->
    whn (Maybe Bool)
  isTopDeg parent gamma deg d reason = case maybeTopDeg of
    Nothing -> return $ Just False
    Just topDeg -> leqDeg parent gamma topDeg deg d reason

  -- | True if @id <= mu . nu@, where nu is the @approxLeftAdjointProj@.
  allowsEta :: forall whn v .
    (MonadWHN sys whn, DeBruijnLevel v) =>
    Constraint sys ->
    Ctx Type sys v Void ->
    ModedModality sys v ->
    Mode sys v {-^ the codomain -} ->
    String ->
    whn (Maybe Bool)
  allowsEta parent gamma dmu@(ModedModality ddom mu) dcod reason = do
    let nu = approxLeftAdjointProj dmu dcod
    let dnu = ModedModality dcod nu
    leqMod parent gamma (idMod dcod) (modality'mod $ compModedModality dmu dnu) dcod dcod reason
