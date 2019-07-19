module Menkar.Systems.Reldtt.MagicContext where

import Prelude hiding (pi)

import Menkar.Basic.Syntax
import Menkar.Fine
--import Menkar.Fine.Multimode
import Menkar.Systems.Reldtt.Basic
import Menkar.Systems.Reldtt.Fine
import Menkar.Basic.Context
import Menkar.Analyzer

import Control.Exception.AssertFalse

import Data.Void
import Data.Functor.Compose
import Data.Proxy
import Data.Number.Nat
import Data.Maybe
import GHC.Generics (U1 (..))
import GHC.Stack

-- | These are de Bruijn LEVELS, not INDICES!!!
var :: (HasCallStack, DeBruijnLevel v) => Nat -> Term Reldtt v
var n = Var2 $ fromMaybe unreachable $ forDeBruijnLevel Proxy n
dvar :: (HasCallStack, DeBruijnLevel v) => Nat -> Mode Reldtt v
dvar n = ReldttMode $ var n
mvar :: (HasCallStack, DeBruijnLevel v) => Nat -> Mode Reldtt v -> Mode Reldtt v -> Modality Reldtt v
mvar n dom cod = ChainModtyTerm dom cod $ var n

val :: Opness -> String -> Modality Reldtt v -> Telescoped Type ValRHS Reldtt v -> Entry Reldtt v
val op str mu rhs = EntryVal $ Declaration
  (DeclNameVal $ Name op str)
  (ModedModality (_chainModty'dom mu) (_chainModty'cod mu) mu)
  Explicit
  rhs

pi :: Segment Type Reldtt v -> Type Reldtt (VarExt v) -> UniHSConstructor Reldtt v
pi aSeg cod = Pi $ Binding aSeg cod
sigma :: Segment Type Reldtt v -> Type Reldtt (VarExt v) -> UniHSConstructor Reldtt v
sigma aSeg cod = Sigma $ Binding aSeg cod
arrow :: Segment Type Reldtt v -> Type Reldtt v -> UniHSConstructor Reldtt v
arrow aSeg cod = pi aSeg (VarWkn <$> cod)

nbind :: Opness -> String -> rhs Reldtt (VarExt v) -> NamedBinding rhs Reldtt v
nbind op str body = NamedBinding (Just $ Name op str) body

seg :: Plicity Reldtt v -> Opness -> String -> Modality Reldtt v -> content Reldtt v -> Segment content Reldtt v
seg plic op str mu content = Declaration
  (DeclNameSegment $ Just $ Name op str)
  (ModedModality (_chainModty'dom mu) (_chainModty'cod mu) mu)
  plic
  content
segIm = seg Implicit
segEx = seg Explicit

moded :: Modality Reldtt v -> ModedModality Reldtt v
moded mu = ModedModality (_chainModty'dom mu) (_chainModty'cod mu) mu

elim :: Term Reldtt v -> UniHSConstructor Reldtt v -> Modality Reldtt v -> Eliminator Reldtt v -> Term Reldtt v
elim eliminee tyEliminee mu eliminator =
  Expr2 $ TermElim (moded mu) eliminee tyEliminee eliminator
app :: Term Reldtt v -> UniHSConstructor Reldtt v -> Mode Reldtt v -> Term Reldtt v -> Term Reldtt v
app eliminee tyEliminee d arg = elim eliminee tyEliminee (idMod d) $ App arg

forget :: Mode Reldtt v -> Modality Reldtt v
forget d = ChainModtyKnown $ KnownModty (ModtySnout 0 0 []) (TailForget d)

----------------------------------------------

-- | @val *id Nat : Set = Nat@
valNat :: Entry Reldtt Void
valNat = val NonOp "Nat" (idMod dataMode) $
  Telescoped (
    ValRHS
      (hs2term NatType)
      (hs2type $ UniHS dataMode)
  )

-- | @val *id suc {n : Nat} : Nat = suc n@
valSuc :: Entry Reldtt Void
valSuc = val NonOp "suc" (idMod dataMode) $
  segEx NonOp "n" (idMod dataMode) (hs2type NatType) :|-
  Telescoped (
    ValRHS
      (Expr2 $ TermCons $ ConsSuc $ var 0)
      (hs2type NatType)
  )

{- | @val *id indNat
        {~ *id dcod : Mode}
        {~ *id mu : Modality d 0}
        *(forget d)
        {C : {*mu n : Nat} -> Set}
        {cz : C 0}
        {cs : {*mu n : Nat} -> C n -> C (suc n)}
        {*mu n0 : Nat} : C n
        = indNat (n > C n) cz (n > ihyp > cs n ihyp) n0@
-}
-- TODO types of cz and cs and rhs need to be lifted to a higher universe
valIndNat :: Entry Reldtt Void
valIndNat = val NonOp "indNat" (idMod dataMode) $
  segIm NonOp "dcod" {- var 0 -} (idMod dataMode) (BareSysType $ SysTypeMode) :|-
  segIm NonOp "mu" {- var 1 -} (idMod dataMode) (BareSysType $ SysTypeModty dataMode (dvar 0)) :|-
  moded (forget $ dvar 0) :**
  segEx NonOp "C" {- var 2 -} (idMod $ dvar 0) (hs2type $ tyMotive) :|-
  segEx NonOp "cz" {- var 3 -} (idMod $ dvar 0) (tyCZ) :|-
  segEx NonOp "cs" {- var 4 -} (idMod $ dvar 0) (hs2type $ tyCS) :|-
  segEx NonOp "n*" {- var 5 -} (mvar 1 dataMode (dvar 0)) (hs2type NatType) :|-
  Telescoped (
    ValRHS
      (elim (var 5) NatType (mvar 1 dataMode (dvar 0)) $ ElimDep
        (nbind NonOp "n" {- var 6 -} $ appMotive (var 6))
        (ElimNat
          (var 3)
          (nbind NonOp "n" {- var 6 -} $ nbind NonOp "ihyp" {- var 7 -} $
            app 
              (app (var 4) (tyCS) (dvar 0) (var 6))
              (tyCS' (var 6))
              (dvar 0)
              (var 7)
          )
        )
      )
      (appMotive (var 5))
  )
  where
    tyMotive :: DeBruijnLevel v => UniHSConstructor Reldtt v
    tyMotive = (segEx NonOp "n" (mvar 1 dataMode (dvar 0)) $ hs2type NatType) `arrow` (hs2type $ UniHS $ dvar 0)
    appMotive :: DeBruijnLevel v => Term Reldtt v -> Type Reldtt v
    appMotive arg = Type $ app (var 2) tyMotive (dvar 0) arg
    tyCZ :: DeBruijnLevel v => Type Reldtt v
    tyCZ = appMotive $ Expr2 $ TermCons $ ConsZero
    tyCS' :: DeBruijnLevel v => Term Reldtt v -> UniHSConstructor Reldtt v
    tyCS' n = (segEx NonOp "ihyp" (idMod $ dvar 0) $ appMotive n)
                     `arrow` (appMotive $ Expr2 $ TermCons $ ConsSuc $ n)
    tyCS :: DeBruijnLevel v => UniHSConstructor Reldtt v
    tyCS = pi (segEx NonOp "n" (mvar 1 dataMode (dvar 0)) $ hs2type NatType) (hs2type $ tyCS' $ Var2 $ VarLast)

{- | @val *id UniHS {*id d : Mode} *(forget d) : UniHS d = UniHS d @
-}
valUniHS :: Entry Reldtt Void
valUniHS = val NonOp "UniHS" (idMod dataMode) $
  segEx NonOp "d" {- var 0 -} (idMod dataMode) (BareSysType $ SysTypeMode) :|-
  moded (forget $ dvar 0) :**
  Telescoped (
    ValRHS
      (hs2term $ UniHS $ dvar 0)
      (hs2type $ UniHS $ dvar 0)
  )

-- | @val *id Unit : Set = Unit@
valUnitType :: Entry Reldtt Void
valUnitType = val NonOp "Unit" (idMod dataMode) $
  Telescoped (
    ValRHS
      (hs2term UnitType)
      (hs2type $ UniHS dataMode)
  )

-- | @val *id unit : Unit = unit@
valUnitTerm :: Entry Reldtt Void
valUnitTerm = val NonOp "unit" (idMod dataMode) $
  Telescoped $ ValRHS (Expr2 $ TermCons $ ConsUnit) (hs2type UnitType)
