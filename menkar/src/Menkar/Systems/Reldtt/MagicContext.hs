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

tyMode :: Type Reldtt v
tyMode = BareSysType $ SysTypeMode
tyModty :: Mode Reldtt v -> Mode Reldtt v -> Type Reldtt v
tyModty dom cod = BareSysType $ SysTypeModty dom cod

comp :: Modality Reldtt v -> Modality Reldtt v -> Modality Reldtt v
comp nu mu = ChainModtyTerm (_chainModty'dom mu) (_chainModty'cod nu) $
  BareModty $ ModtyTermComp
  (_chainModty'cod nu)
  nu
  (_chainModty'dom nu)
  mu
  (_chainModty'dom mu)

----------------------------------------------

-- | @val *id Nat : Set = Nat@
valNat :: Entry Reldtt Void
valNat = val NonOp "Nat" (idMod dataMode) $
  segIm NonOp "d" {- var 0 -} (idMod dataMode) tyMode :|-
  moded (forget $ dvar 0) :**
  Telescoped (
    ValRHS
      (hs2term NatType)
      (hs2type $ UniHS $ dvar 0)
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
        {~ *id dmot : Mode}
        {~ *id nu : Modality d 0}
        *(forget d)
        {C : {*nu n : Nat} -> Set}
        {cz : C 0}
        {cs : {*nu n : Nat} -> C n -> C (suc n)}
        {*nu n0 : Nat} : C n
        = indNat (n > C n) cz (n > ihyp > cs n ihyp) n0@
-}
-- TODO types of cz and cs and rhs need to be lifted to a higher universe
valIndNat :: Entry Reldtt Void
valIndNat = val NonOp "indNat" (idMod dataMode) $
  segIm NonOp "dmot" {- var 0 -} (idMod dataMode) (tyMode) :|-
  segIm NonOp "nu" {- var 1 -} (idMod dataMode) (tyModty dataMode (dvar 0)) :|-
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

-----------------

{- | @val *id UniHS {*id d : Mode} *(forget d) : UniHS d = UniHS d @
-}
valUniHS :: Entry Reldtt Void
valUniHS = val NonOp "UniHS" (idMod dataMode) $
  segEx NonOp "d" {- var 0 -} (idMod dataMode) tyMode :|-
  moded (forget $ dvar 0) :**
  Telescoped (
    ValRHS
      (hs2term $ UniHS $ dvar 0)
      (hs2type $ UniHS $ dvar 0)
  )

-----------------

-- | @val *id Unit : Set = Unit@
valUnitType :: Entry Reldtt Void
valUnitType = val NonOp "Unit" (idMod dataMode) $
  segIm NonOp "d" {- var 0 -} (idMod dataMode) tyMode :|-
  moded (forget $ dvar 0) :**
  Telescoped (
    ValRHS
      (hs2term UnitType)
      (hs2type $ UniHS $ dvar 0)
  )

-- | @val *id unit {~ *id d : Mode} {*(forget d)} : Unit = unit@
valUnitTerm :: Entry Reldtt Void
valUnitTerm = val NonOp "unit" (idMod dataMode) $
  segIm NonOp "d" {- var 0 -} (idMod dataMode) tyMode :|-
  moded (forget $ dvar 0) :**
  Telescoped (
    ValRHS
      (Expr2 $ TermCons $ ConsUnit)
      (hs2type UnitType)
  )

-----------------

{-
{- | @val *id box
        {~ *id ddom dcod : Mode}
        {~ *id mu : Modality dom cod}
        *(forget cod)
        {~ *mu X : UniHS dom}
        {x : X} : Box {*mu _ : X} = box x@
-}
valBoxTerm :: Entry Reldtt Void
valBoxTerm = val NonOp "box" (idMod dataMode) $
  segIm NonOp "ddom" {- var 0 -} (idMod dataMode) tyMode :|-
  segIm NonOp "dcod" {- var 1 -} (idMod dataMode) tyMode :|-
  segIm NonOp "mu" {- var 2 -} (idMod dataMode) (tyModty (dvar 0) (dvar 1)) :|-
  moded (forget $ dvar 1) :**
  segIm NonOp "X" {- var 0 -} (hs2type $ UniHS TrivMode) :|-
  segEx NonOp "x" {- var 1 -} (Type $ var 0) :|-
  Telescoped (
    ValRHS
      (Expr2 $ TermCons $ ConsBox boxSeg $ var 1)
      (hs2type $ BoxType $ boxSeg)
  )
  where boxSeg :: DeBruijnLevel v => Segment Type Reldtt v
        boxSeg = segEx NonOp "x" $ Type $ var 0
-}

{-| val *id indBox
      {~ *id ddom dcod dmot : Mode}
      {~ *id mu : Modality ddom dcod}
      {~ *id nu : Modality dcod dmot}
      {*(forget dmot)}
      {&ddom *(nu @ mu) X : UniHS ddom}
      {&dmot C : {&dcod *mu _ : {*nu} -> X} -> UniHS dmot}
      {&dmot cbox : {*(nu @ mu) x : X} -> C ({*nu} > x)}
      {&dcod b0 : {*nu} -> X} : C b0
        = indBox (b > C b) (x > cbox x) b0
-}
valIndBox :: Entry Reldtt Void
valIndBox = val NonOp "indBox" (idMod dataMode) $
  segIm NonOp "ddom" {- var 0 -} (idMod dataMode) tyMode :|-
  segIm NonOp "dcod" {- var 1 -} (idMod dataMode) tyMode :|-
  segIm NonOp "dmot" {- var 2 -} (idMod dataMode) tyMode :|-
  segIm NonOp "mu" {- var 3 -} (idMod dataMode) (tyModty (dvar 0) (dvar 1)) :|-
  segIm NonOp "nu" {- var 4 -} (idMod dataMode) (tyModty (dvar 1) (dvar 2)) :|-
  moded (forget $ dvar 2) :**
  segEx NonOp "X"  {- var 5 -} (comp (mvar 4 (dvar 1) (dvar 2)) (mvar 3 (dvar 0) (dvar 1))) (hs2type $ UniHS $ dvar 0) :|-
  segEx NonOp "C"  {- var 6 -} (idMod $ dvar 2) (hs2type tyMotive) :|-
  segEx NonOp "cbox" {- var 7 -} (idMod $ dvar 2) (hs2type $ tyCBox) :|-
  segEx NonOp "b*" {- var 8 -} (idMod $ dvar 2) (hs2type $ BoxType $ boxSeg) :|-
  Telescoped (
    ValRHS
      (elim (var 8) (BoxType $ boxSeg) (mvar 4 (dvar 1) (dvar 2))
      $ ElimDep
        (nbind NonOp "b" {- var 9 -} $ appMotive $ var 5)
      $ ElimBox
        (nbind NonOp "x" {- var 9 -} $ app (var 7) tyCBox (dvar 2) (var 9))
      )
      (appMotive $ var 8)
  )
  where
    boxSeg :: DeBruijnLevel v => Segment Type Reldtt v
    boxSeg = segEx NonOp "x" (mvar 3 (dvar 0) (dvar 1)) $ Type $ var 5
    tyMotive :: DeBruijnLevel v => UniHSConstructor Reldtt v
    tyMotive = (segEx NonOp "b" (mvar 4 (dvar 1) (dvar 2)) (hs2type $ BoxType $ boxSeg)) `arrow` (hs2type $ UniHS $ dvar 2)
    appMotive :: DeBruijnLevel v => Term Reldtt v -> Type Reldtt v
    appMotive arg = Type $ app (var 6) tyMotive (dvar 2) arg
    tyCBox :: DeBruijnLevel v => UniHSConstructor Reldtt v
    tyCBox = pi (segEx NonOp "x" (comp (mvar 4 (dvar 1) (dvar 2)) (mvar 3 (dvar 0) (dvar 1))) (Type $ var 5)) $
             appMotive $ Expr2 $ TermCons $ ConsBox boxSeg $ Var2 $ VarLast

-----------------

{-| val *id (,)
      {~ *id ddom dcod : Mode}
      {~ *id mu : Modality ddom dcod}
      *(forget dcod)
      {~ *mu A : UniHS ddom}
      {~ *id B : {*mu A} -> UniHS dcod}
      {*mu x : A}
      {*id y : B x}
      : {*mu x : A} >< B x
      = x , y
-}
valPair :: Entry Reldtt Void
valPair = val Op "," (idMod dataMode) $
  segIm NonOp "ddom" {- var 0 -} (idMod dataMode) tyMode :|-
  segIm NonOp "dcod" {- var 1 -} (idMod dataMode) tyMode :|-
  segIm NonOp "mu" {- var 2 -} (idMod dataMode) (tyModty (dvar 0) (dvar 1)) :|-
  moded (forget $ dvar 1) :**
  segIm NonOp "A" {- var 3 -} (mvar 2 (dvar 0) (dvar 1)) (hs2type $ UniHS $ dvar 0) :|-
  segIm NonOp "B" {- var 4 -} (idMod $ dvar 1) (hs2type $ tyCod) :|-
  segEx NonOp "x" {- var 5 -} (mvar 2 (dvar 0) (dvar 1)) (Type $ var 3) :|-
  segEx NonOp "y" {- var 6 -} (idMod $ dvar 1) (appCod $ var 5) :|-
  Telescoped (
    ValRHS
      (Expr2 $ TermCons $ Pair (Binding segA $ appCod $ Var2 VarLast) (var 5) (var 6))
      (hs2type $ sigma segA {- var 7 -} (appCod $ var 7))
  )
  where
    segA :: DeBruijnLevel v => Segment Type Reldtt v
    segA = segEx NonOp "x" (mvar 2 (dvar 0) (dvar 1)) (Type $ var 3)
    tyCod :: DeBruijnLevel v => UniHSConstructor Reldtt v
    tyCod = segA `arrow` (hs2type $ UniHS $ dvar 1)
    appCod :: DeBruijnLevel v => Term Reldtt v -> Type Reldtt v
    appCod arg = Type $ app (var 4) tyCod (dvar 1) arg

{-| val *id indPair
      {~ *id ddom dcod dmot : Mode}
      {~ *id mu : Modality ddom dcod}
      {~ *id nu : Modality dcod dmot}
      {*(forget dmot)}
      {~ *(nu @ mu) A : UniHS ddom}
      {~ *nu B : A -> UniHS dcod}
      {*id C : {*nu _ : {*mu x : A} >< B x} -> Set}
      {*id cpair : {*(nu @ mu) x : A} {*nu y : B x} -> C (x , y)}
      {*nu p0 : {*mu x : A} >< B x}
      : C p0
      = indPair (p > C) (x > y > cpair x y) p0
-}
valIndPair :: Entry Reldtt Void
valIndPair = val NonOp "indPair" (idMod dataMode) $
  segIm NonOp "ddom" {- var 0 -} (idMod dataMode) tyMode :|-
  segIm NonOp "dcod" {- var 1 -} (idMod dataMode) tyMode :|-
  segIm NonOp "dmot" {- var 2 -} (idMod dataMode) tyMode :|-
  segIm NonOp "mu" {- var 3 -} (idMod dataMode) (tyModty (dvar 0) (dvar 1)) :|-
  segIm NonOp "nu" {- var 4 -} (idMod dataMode) (tyModty (dvar 1) (dvar 2)) :|-
  moded (forget $ dvar 2) :**
  segIm NonOp "A" {- var 5 -} (comp (mvar 4 (dvar 1) (dvar 2)) (mvar 3 (dvar 0) (dvar 1))) (hs2type $ UniHS $ dvar 0) :|-
  segIm NonOp "B" {- var 6 -} (mvar 4 (dvar 1) (dvar 2)) (hs2type $ tyCod) :|-
  segEx NonOp "C" {- var 7 -} (idMod $ dvar 2) (hs2type $ tyMotive) :|-
  segEx NonOp "cpair" {- var 8 -} (idMod $ dvar 2) (hs2type $ tyCPair) :|-
  segEx NonOp "p*" {- var 9 -} (mvar 4 (dvar 1) (dvar 2)) (hs2type $ tyPair) :|-
  Telescoped (
    ValRHS
      (elim (var 9) tyPair (mvar 4 (dvar 1) (dvar 2)) $
       ElimDep (nbind NonOp "p" {- var 10 -} $ appMotive $ var 10) $
       ElimSigma $ nbind NonOp "x" {- var 10 -} $ nbind NonOp "y" {- var 11 -} $
       app (
         app (var 8) tyCPair (dvar 2) (var 10)
       ) (tyCPair' (var 10)) (dvar 2) (var 11)
      )
      (appMotive $ var 9)
  )
  where
    segAMu :: DeBruijnLevel v => Segment Type Reldtt v
    segAMu = segEx NonOp "x" (mvar 3 (dvar 0) (dvar 1)) (Type $ var 5)
    segAMuNu :: DeBruijnLevel v => Segment Type Reldtt v
    segAMuNu = segEx NonOp "x" (comp (mvar 4 (dvar 1) (dvar 2)) (mvar 3 (dvar 0) (dvar 1))) (Type $ var 5)
    tyCod :: DeBruijnLevel v => UniHSConstructor Reldtt v
    tyCod = segAMu `arrow` (hs2type $ UniHS $ dvar 1)
    appCod :: DeBruijnLevel v => Term Reldtt v -> Type Reldtt v
    appCod arg = Type $ app (var 6) tyCod (dvar 1) arg
    tyPair :: DeBruijnLevel v => UniHSConstructor Reldtt v
    tyPair = sigma segAMu $ appCod $ Var2 $ VarLast
    tyMotive :: DeBruijnLevel v => UniHSConstructor Reldtt v
    tyMotive = (segEx NonOp "p" (mvar 4 (dvar 1) (dvar 2)) $ hs2type tyPair) `arrow` (hs2type $ UniHS $ dvar 2)
    appMotive :: DeBruijnLevel v => Term Reldtt v -> Type Reldtt v
    appMotive arg = Type $ app (var 7) tyMotive (dvar 2) arg
    tyCPair' :: DeBruijnLevel v => Term Reldtt v -> UniHSConstructor Reldtt v
    tyCPair' x = pi
      (segEx NonOp "y" (mvar 4 (dvar 1) (dvar 2)) $ appCod $ x)
      (appMotive $ Expr2 $ TermCons $ Pair (Binding segAMu $ appCod $ Var2 VarLast) (VarWkn <$> x) (Var2 VarLast))
    tyCPair :: DeBruijnLevel v => UniHSConstructor Reldtt v
    tyCPair = pi segAMuNu $ hs2type $ tyCPair' $ Var2 $ VarLast

-----------------

-- | @val *id Empty {~ *id d : Mode} {*(forget d)} : UniHS d = Empty@
valEmpty :: Entry Reldtt Void
valEmpty = val NonOp "Empty" (idMod dataMode) $
  segIm NonOp "d" {- var 0 -} (idMod dataMode) tyMode :|-
  moded (forget $ dvar 0) :**
  Telescoped (
    ValRHS
      (hs2term EmptyType)
      (hs2type $ UniHS $ dvar 0)
  )

-----------------
