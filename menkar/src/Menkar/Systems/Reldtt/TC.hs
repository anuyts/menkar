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
        ModeTermFinite t -> do
          addNewConstraint
            (JudTerm gamma t (hs2type NatType))
            (Just parent)
            "Checking argument."
        ModeTermOmega -> return ()
      
    SysTermModty mu -> do
      -- check contents and extract (co)domain
      (ddom, dcod) <- case mu of
        ModtyTermChain chmu -> _
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
          return (ddom, dcod)
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
