module Menkar.Systems.Reldtt.TC where

import Menkar.Basic
import Menkar.WHN
import Menkar.System.Fine
import Menkar.System.Scoper
import Menkar.System.WHN
import Menkar.System.TC
import Menkar.Fine
import Menkar.Monad
import Menkar.Systems.Reldtt.Fine
import Menkar.Systems.Reldtt.Scoper
import Menkar.Systems.Reldtt.WHN

import Control.Exception.AssertFalse

import Data.Void
import Data.Functor.Compose
import Control.Lens
import GHC.Generics

{-| Returns the codomain and domain IN THAT ORDER.
-}
checkKnownModty :: forall tc v .
  (MonadTC Reldtt tc, DeBruijnLevel v) =>
  Constraint Reldtt ->
  Ctx Type Reldtt v Void ->
  KnownModty v ->
  tc (Term Reldtt v, Term Reldtt v)
checkKnownModty parent gamma kmu@(KnownModty snout tail) = do
  case tail of
    TailEmpty -> return ()
    TailDisc dcod -> do
      addNewConstraint
        (JudTerm gamma dcod (BareSysType SysTypeMode))
        (Just parent)
        "Checking codomain of modality tail."
    TailForget ddom -> do
      addNewConstraint
        (JudTerm gamma ddom (BareSysType SysTypeMode))
        (Just parent)
        "Checking domain of modality tail."
    TailDiscForget ddom dcod -> do
      addNewConstraint
        (JudTerm gamma ddom (BareSysType SysTypeMode))
        (Just parent)
        "Checking domain of modality tail."
      addNewConstraint
        (JudTerm gamma dcod (BareSysType SysTypeMode))
        (Just parent)
        "Checking codomain of modality tail."
    TailCont d ->
      addNewConstraint
        (JudTerm gamma d (BareSysType SysTypeMode))
        (Just parent)
        "Checking (co)domain of modality tail."
    TailProblem -> tcFail parent "Erroneous tail."
  return (_knownModty'cod kmu, _knownModty'dom kmu)

checkChainModty :: forall tc v .
  (MonadTC Reldtt tc, DeBruijnLevel v) =>
  Constraint Reldtt ->
  Ctx Type Reldtt v Void ->
  ChainModty v ->
  tc (Term Reldtt v, Term Reldtt v)
checkChainModty parent gamma chainModty@(ChainModty kmu (Compose remainder)) = case remainder of
  [] -> checkKnownModty parent gamma kmu
  _:_ -> do
    (dcod, d1) <- checkKnownModty parent gamma kmu
    codsNdomsKnowns <- sequenceA $ checkKnownModty parent gamma . snd1 <$> remainder
    let codsKnowns = fst <$> codsNdomsKnowns
    let domsKnowns = snd <$> codsNdomsKnowns
    let domsNeutrals = codsKnowns
    let codsNeutrals = d1 : init domsKnowns
    sequenceA $ zip3 codsNeutrals domsNeutrals remainder <&>
      \ (dcodNeutral, ddomNeutral, (rhoNeutral :*: _)) -> do
        addNewConstraint
          (JudTerm gamma rhoNeutral (BareSysType $ SysTypeModty ddomNeutral dcodNeutral))
          (Just parent)
          "Type-checking a constituent modality."
    return (dcod, last domsKnowns)

instance SysTC Reldtt where
  
  checkTermSys parent gamma t ty = case t of
    
    SysTermMode d -> do
      addNewConstraint
        (JudTypeRel
          eqDeg
          (duplicateCtx gamma)
          (Twice2 (BareSysType SysTypeMode) ty)
        )
        (Just parent)
        "Checking that actual type equals expected type."
      case d of
        ModeTermZero -> return ()
        ModeTermSuc d -> do
          addNewConstraint
            (JudTerm gamma d (BareSysType SysTypeMode))
            (Just parent)
            "Checking argument."
        ModeTermOmega -> return ()
      
    SysTermModty mu -> do
      -- check contents and extract (co)domain
      (dcod, ddom) <- case mu of
        ModtyTermChain chmu -> checkChainModty parent gamma chmu
        ModtyTermDiv rho nu -> unreachable -- only for prettyprinting
        ModtyTermApproxLeftAdjointProj ddom dcod nu -> do
          addNewConstraint
            (JudTerm gamma ddom (BareSysType $ SysTypeMode))
            (Just parent)
            "Checking domain."
          addNewConstraint
            (JudTerm gamma dcod (BareSysType $ SysTypeMode))
            (Just parent)
            "Checking codomain."
          addNewConstraint
            (JudTerm gamma nu (BareSysType $ SysTypeModty dcod ddom))
            (Just parent)
            "Checking argument modality."
          return (dcod, ddom)
        ModtyTermUnavailable ddom dcod -> unreachable -- only for prettyprinting
          {-do
          addNewConstraint
            (JudTerm gamma ddom (BareSysType $ SysTypeMode))
            (Just parent)
            "Checking domain."
          addNewConstraint
            (JudTerm gamma dcod (BareSysType $ SysTypeMode))
            (Just parent)
            "Checking codomain."
          return (ddom, dcod)-}
      addNewConstraint
        (JudTypeRel
          eqDeg
          (duplicateCtx gamma)
          (Twice2 (BareSysType $ SysTypeModty ddom dcod) ty)
        )
        (Just parent)
        "Checking that actual type equals expected type."
      
    SysTermDeg deg -> do
      case deg of
        DegKnown kdeg -> do
          _
          --case kdeg of
          --  KnownDegProblem 
        DegGet deg mu ddom dcod -> _
