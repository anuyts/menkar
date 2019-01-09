module Menkar.Fine.Multimode.Trivial.MagicContext where

import Prelude hiding (pi)

import Menkar.Basic.Syntax
import Menkar.Fine.Syntax
import Menkar.Fine.Context
import Menkar.Fine.Judgement
--import Menkar.Fine.Multimode
import Menkar.Fine.Multimode.Trivial.Trivial
import Menkar.Basic.Context

import Control.Exception.AssertFalse

import Data.Void
import Data.Functor.Compose
import Data.Proxy
import Data.Number.Nat
import Data.Maybe
import GHC.Generics (U1 (..))

-- | These are de Bruijn LEVELS, not INDICES!!!
var :: DeBruijnLevel v => Nat -> Term U1 U1 v
var n = Var3 $ fromMaybe unreachable $ forDeBruijnLevel Proxy n

val :: Opness -> String -> Telescoped Type ValRHS U1 U1 v -> Entry U1 U1 v
val op str rhs = EntryVal $ Declaration
  (DeclNameVal $ Name op str)
  trivModedModality
  Explicit
  rhs

pi :: Segment Type U1 U1 v -> Type U1 U1 (VarExt v) -> UniHSConstructor U1 U1 v
pi aSeg cod = Pi $ Binding aSeg (unType cod)
arrow :: Segment Type U1 U1 v -> Type U1 U1 v -> UniHSConstructor U1 U1 v
arrow aSeg cod = pi aSeg (VarWkn <$> cod)

nbind :: Opness -> String -> rhs U1 U1 (VarExt v) -> NamedBinding rhs U1 U1 v
nbind op str body = NamedBinding (Just $ Name op str) body

seg :: Plicity U1 U1 v -> Opness -> String -> content U1 U1 v -> Segment content U1 U1 v
seg plic op str content = Declaration
  (DeclNameSegment $ Just $ Name op str)
  trivModedModality
  plic
  content
segIm = seg Implicit
segEx = seg Explicit

elim :: Term U1 U1 v -> UniHSConstructor U1 U1 v -> Eliminator U1 U1 v -> Term U1 U1 v
elim eliminee tyEliminee eliminator = Expr3 $ TermElim trivModedModality eliminee tyEliminee eliminator
app :: Term U1 U1 v -> UniHSConstructor U1 U1 v -> Term U1 U1 v -> Term U1 U1 v
app eliminee tyEliminee arg = elim eliminee tyEliminee $ App arg

----------------------------------------------

-- | @Nat {~ | l : Nat} : Set l = Nat@
valNat :: Entry U1 U1 Void
valNat = val NonOp "Nat" $
  segIm NonOp "l" (hs2type NatType) :|-
  Telescoped (
    ValRHS
      (hs2term NatType)
      (hs2type $ UniHS U1 $ var 0)
  )

-- | @suc {n : Nat} : Nat = suc n@
valSuc :: Entry U1 U1 Void
valSuc = val NonOp "suc" $
  segEx NonOp "n" (hs2type NatType) :|-
  Telescoped (
    ValRHS
      (Expr3 $ TermCons $ ConsSuc $ var 0)
      (hs2type NatType)
  )

{- | @indNat {~ | l : Nat} {C : Nat -> Set l} {cz : C 0} {cs : {n : Nat} -> C n -> C (suc n)} {n0 : Nat} : C n
        = indNat (n > C n) cz (n > ihyp > cs n ihyp) n0@
-}
-- TODO types of cz and cs and rhs need to be lifted to a higher universe
valIndNat :: Entry U1 U1 Void
valIndNat = val NonOp "indNat" $
  segIm NonOp "l" {- var 0 -} (hs2type NatType) :|-
  segEx NonOp "C" {- var 1 -} (hs2type $ tyMotive) :|-
  segEx NonOp "cz" {- var 2 -} (tyCZ) :|-
  segEx NonOp "cs" {- var 3 -} (hs2type $ tyCS) :|-
  segEx NonOp "n0" {- var 4 -} (hs2type NatType) :|-
  Telescoped (
    ValRHS
      (elim (var 0) NatType $ ElimDep
        (nbind NonOp "n" {- var 5 -} $ appMotive (var 5))
        (ElimNat
          (var 2)
          (nbind NonOp "n" {- var 5 -} $ nbind NonOp "ihyp" {- var 6 -} $
            app
              (app (var 3) (tyCS) (var 5))
              (tyCS' (var 5))
              (var 6)
          )
        )
      )
      (appMotive (var 4))
  )
  where
    tyMotive :: DeBruijnLevel v => UniHSConstructor U1 U1 v
    tyMotive = (segEx NonOp "n" $ hs2type NatType) `arrow` (hs2type $ UniHS U1 $ var 0)
    appMotive :: DeBruijnLevel v => Term U1 U1 v -> Type U1 U1 v
    appMotive arg = Type $ app (var 1) tyMotive arg
    tyCZ :: DeBruijnLevel v => Type U1 U1 v
    tyCZ = appMotive $ Expr3 $ TermCons $ ConsZero
    tyCS' :: DeBruijnLevel v => Term U1 U1 v -> UniHSConstructor U1 U1 v
    tyCS' n = (segEx NonOp "ihyp" $ appMotive n)
                     `arrow` (appMotive $ Expr3 $ TermCons $ ConsSuc $ n)
    tyCS :: DeBruijnLevel v => UniHSConstructor U1 U1 v
    tyCS = pi (segEx NonOp "n" $ hs2type NatType) (hs2type $ tyCS' $ Var3 $ VarLast)

{- | @UniHS {l : Nat} : UniHS (suc l) = UniHS l@
-}
valUniHS :: Entry U1 U1 Void
valUniHS = val NonOp "UniHS" $
  segEx NonOp "l" {- var 0 -} (hs2type NatType) :|-
  Telescoped (
    ValRHS
      (hs2term $ UniHS U1 $ var 0)
      (hs2type $ UniHS U1 $ Expr3 $ TermCons $ ConsSuc $ var 0)
  )

-- | @Unit {~ | l : Nat} : Set l = Unit@
valUnitType :: Entry U1 U1 Void
valUnitType = val NonOp "Unit" $
  segIm NonOp "l" (hs2type NatType) :|-
  Telescoped (
    ValRHS
      (hs2term UnitType)
      (hs2type $ UniHS U1 $ var 0)
  )

-- | @unit : Unit = unit@
valUnitTerm :: Entry U1 U1 Void
valUnitTerm = val NonOp "unit" $ Telescoped $ ValRHS (Expr3 $ TermCons $ ConsUnit) (hs2type UnitType)

-- | @Box {~ | l : Nat} {X : UniHS l} : UniHS l = Box {x : X}@
valBoxType :: Entry U1 U1 Void
valBoxType = val NonOp "Box" $
  segIm NonOp "l" {- var 0 -} (hs2type NatType) :|-
  segEx NonOp "X" {- var 1 -} (hs2type $ UniHS U1 $ var 0) :|-
  Telescoped (
    ValRHS
      (hs2term $ BoxType $ segEx NonOp "x" $ Type $ var 1)
      (hs2type $ UniHS U1 $ var 0)
  )

-- | @box {~ | l : Nat} {~ | X : UniHS l} {x : X} : Box X = box x@
valBoxTerm :: Entry U1 U1 Void
valBoxTerm = val NonOp "box" $
  segIm NonOp "l" {- var 0 -} (hs2type NatType) :|-
  segIm NonOp "X" {- var 1 -} (hs2type $ UniHS U1 $ var 0) :|-
  segEx NonOp "x" {- var 2 -} (Type $ var 1) :|-
  Telescoped (
    ValRHS
      (Expr3 $ TermCons $ ConsBox boxSeg $ var 2)
      (hs2type $ BoxType $ boxSeg)
  )
  where boxSeg :: DeBruijnLevel v => Segment Type U1 U1 v
        boxSeg = segEx NonOp "x" $ Type $ var 1

{-| indBox
      {~ | lX lC : Nat}
      {X : Set lX}
      {C : Box X -> Set lC}
      {cbox : {x : X} -> C (box x)}
      {b0 : Box X} : C b0
        = indBox (b > C b) (x > cbox x) b0
-}
valIndBox :: Entry U1 U1 Void
valIndBox = val NonOp "indBox" $
  segIm NonOp "lX" {- var 0 -} (hs2type NatType) :|-
  segIm NonOp "lC" {- var 1 -} (hs2type NatType) :|-
  segEx NonOp "X"  {- var 2 -} (hs2type $ UniHS U1 $ var 0) :|-
  segEx NonOp "C"  {- var 3 -} (hs2type tyMotive) :|-
  segEx NonOp "cbox" {- var 4 -} (hs2type $ tyCBox) :|-
  segEx NonOp "b0" {- var 5 -} (hs2type $ BoxType $ boxSeg) :|-
  Telescoped (
    ValRHS
      (elim
        (var 5)
        (BoxType $ boxSeg)
      $ ElimDep
        (nbind NonOp "b" {- var 6 -} $ appMotive $ var 6)
      $ ElimBox
        (nbind NonOp "x" {- var 6 -} $ app (var 4) tyCBox (var 6))
      )
      (appMotive $ var 5)
  )
  where
    boxSeg :: DeBruijnLevel v => Segment Type U1 U1 v
    boxSeg = segEx NonOp "x" $ Type $ var 2
    tyMotive :: DeBruijnLevel v => UniHSConstructor U1 U1 v
    tyMotive = (segEx NonOp "b" (hs2type $ BoxType $ boxSeg)) `arrow` (hs2type $ UniHS U1 $ var 1)
    appMotive :: DeBruijnLevel v => Term U1 U1 v -> Type U1 U1 v
    appMotive arg = Type $ app (var 3) tyMotive arg
    tyCBox :: DeBruijnLevel v => UniHSConstructor U1 U1 v
    tyCBox = pi (segEx NonOp "x" (Type $ var 2)) $ appMotive $ Expr3 $ TermCons $ ConsBox boxSeg $ Var3 $ VarLast

----------------------------------------------

magicEntries :: [Entry U1 U1 Void]
magicEntries = 
  valNat :
  valSuc :
  valIndNat : -- doesn't type-check
  valUniHS : -- doesn't type-check
  valUnitType :
  valUnitTerm :
  valBoxType :
  valBoxTerm :
  valIndBox :
  []

magicContext :: Ctx Type U1 U1 (VarInModule Void) Void
magicContext = CtxEmpty U1 :<...> ModuleRHS (absurd <$> (Compose $ reverse magicEntries))

----------------------------------------------

magicModuleCorrect :: Judgement U1 U1 U1
magicModuleCorrect = 
    (JudModule
      (CtxEmpty U1)
      (Declaration
        (DeclNameModule "magic")
        trivModedModality
        Explicit $
       Telescoped $ ModuleRHS $ absurd <$> (Compose $ reverse magicEntries)
      )
    )
