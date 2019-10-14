module Menkar.System.WHN where

import Menkar.System.Fine
import Menkar.System.Scoper
import Menkar.System.Analyzer
import Menkar.Fine
import Menkar.Monad.Monad
import Menkar.Analyzer

import Control.Exception.AssertFalse

import Data.Void
import Control.Monad.Writer
import GHC.Generics

class (SysScoper sys, SysAnalyzer sys) => SysWHN sys where
  whnormalizeSysTerm :: forall whn v .
    (MonadWHN sys whn, MonadWriter [Int] whn, DeBruijnLevel v) =>
    SysTerm sys v ->
    Type sys v ->
    String ->
    whn (Term sys v)
  whnormalizeMultimodeOrSysAST :: forall whn t v .
    (MonadWHN sys whn, MonadWriter [Int] whn, DeBruijnLevel v) =>
    MultimodeOrSysAnalyzableToken sys t ->
    t v ->
    ClassifExtraInput t v ->
    Classif t v ->
    String ->
    whn (t v)
        
  {-| @'leqMod' ddom dcod mu1 mu2@ returns whether @mu1 <= mu2@, or
      @'Nothing'@ if it is presently unclear.
      This method may call @'awaitMeta'@.
      This method should be efficient and can be ridiculously strict; the relation should probably be transitive,
      but reflexivity is not even required. It should imply validity of the inequality judgement.
  -}
  leqMod :: forall whn v .
    (MonadWHN sys whn, DeBruijnLevel v) =>
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
    Degree sys v -> 
    Degree sys v -> 
    Mode sys v ->
    String ->
    whn (Maybe Bool)
    
  isEqDeg :: forall whn v .
    (MonadWHN sys whn, DeBruijnLevel v) =>
    Degree sys v -> 
    Mode sys v ->
    String ->
    whn (Maybe Bool)
  isEqDeg deg d reason = leqDeg deg (eqDeg d) d reason

  isTopDeg :: forall whn v .
    (MonadWHN sys whn, DeBruijnLevel v) =>
    Degree sys v -> 
    Mode sys v ->
    String ->
    whn (Maybe Bool)
  isTopDeg deg d reason = case maybeTopDeg d of
    Nothing -> return $ Just False
    Just topDeg -> leqDeg topDeg deg d reason

  -- | True if @id <= mu . nu@, where nu is the @approxLeftAdjointProj@.
  -- | Should at least imply that @nu . mu <= id@ as a judgemental inequality.
  allowsEta :: forall whn v .
    (MonadWHN sys whn, DeBruijnLevel v) =>
    ModedModality sys v ->
    --Mode sys v {-^ the codomain -} ->
    String ->
    whn (Maybe Bool)
  allowsEta dmu@(ModedModality ddom dcod' mu) {-dcod-} reason = do
    let dnu = modedApproxLeftAdjointProj dmu
    leqMod (idMod dcod') (_modality'mod $ compModedModality dmu dnu) dcod' dcod' reason
  allowsEta _ reason = unreachable

  {- Use the inequality judgement instead!
  -- | True if @nu . mu <= id@, where nu is the @approxLeftAdjointProj@.
  -- | Categorically, this should always be true if @nu@ exists, but here by @<=@ we mean @leqMod@, which may be
  -- | very strict.
  allowsProjections :: forall whn v .
    (MonadWHN sys whn, DeBruijnLevel v) =>
    Constraint sys ->
    Ctx Type sys v ->
    ModedModality sys v ->
    Mode sys v {-^ the codomain -} ->
    String ->
    whn (Maybe Bool)
  allowsProjections parent gamma dmu@(ModedModality ddom mu) dcod reason = do
    let dnu = modedApproxLeftAdjointProj dmu dcod
    leqMod parent gamma (_modality'mod $ compModedModality dnu dmu) (idMod ddom) ddom ddom reason
  -}


whnormalizeMode :: forall sys whn v .
    (SysWHN sys, MonadWHN sys whn, MonadWriter [Int] whn, DeBruijnLevel v) =>
    Mode sys v ->
    String ->
    whn (Mode sys v)
whnormalizeMode d reason =
  whnormalizeMultimodeOrSysAST (Left AnTokenMode) d U1 U1 reason
whnormalizeModality :: forall sys whn v .
    (SysWHN sys, MonadWHN sys whn, MonadWriter [Int] whn, DeBruijnLevel v) =>
    Modality sys v ->
    Mode sys v ->
    Mode sys v ->
    String ->
    whn (Modality sys v)
whnormalizeModality mu dom cod reason =
  whnormalizeMultimodeOrSysAST (Left AnTokenModality) mu U1 (dom :*: cod) reason
whnormalizeDegree :: forall sys whn v .
    (SysWHN sys, MonadWHN sys whn, MonadWriter [Int] whn, DeBruijnLevel v) =>
    Degree sys v ->
    Mode sys v ->
    String ->
    whn (Degree sys v)
whnormalizeDegree deg d reason =
  whnormalizeMultimodeOrSysAST (Left AnTokenDegree) deg U1 d reason
