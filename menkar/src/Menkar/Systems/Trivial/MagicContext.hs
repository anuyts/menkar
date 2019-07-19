module Menkar.Systems.Trivial.MagicContext where

import Prelude hiding (pi)

import Menkar.Basic.Syntax
import Menkar.Fine.Syntax
import Menkar.Fine.Context
import Menkar.Fine.Judgement
--import Menkar.Fine.Multimode
import Menkar.Systems.Trivial.Trivial
import Menkar.Basic.Context
import Menkar.System

import Control.Exception.AssertFalse

import Data.Void
import Data.Functor.Compose
import Data.Proxy
import Data.Number.Nat
import Data.Maybe
import GHC.Generics (U1 (..))
import GHC.Stack

-- | These are de Bruijn LEVELS, not INDICES!!!
var :: (HasCallStack, DeBruijnLevel v) => Nat -> Term Trivial v
var n = Var2 $ fromMaybe unreachable $ forDeBruijnLevel Proxy n

val :: Opness -> String -> Telescoped Type ValRHS Trivial v -> Entry Trivial v
val op str rhs = EntryVal $ Declaration
  (DeclNameVal $ Name op str)
  trivModedModality
  Explicit
  rhs

pi :: Segment Type Trivial v -> Type Trivial (VarExt v) -> UniHSConstructor Trivial v
pi aSeg cod = Pi $ Binding aSeg cod
sigma :: Segment Type Trivial v -> Type Trivial (VarExt v) -> UniHSConstructor Trivial v
sigma aSeg cod = Sigma $ Binding aSeg cod
arrow :: Segment Type Trivial v -> Type Trivial v -> UniHSConstructor Trivial v
arrow aSeg cod = pi aSeg (VarWkn <$> cod)

nbind :: Opness -> String -> rhs Trivial (VarExt v) -> NamedBinding rhs Trivial v
nbind op str body = NamedBinding (Just $ Name op str) body

seg :: Plicity Trivial v -> Opness -> String -> content Trivial v -> Segment content Trivial v
seg plic op str content = Declaration
  (DeclNameSegment $ Just $ Name op str)
  trivModedModality
  plic
  content
segIm = seg Implicit
segEx = seg Explicit

elim :: Term Trivial v -> UniHSConstructor Trivial v -> Eliminator Trivial v -> Term Trivial v
elim eliminee tyEliminee eliminator = Expr2 $ TermElim trivModedModality eliminee tyEliminee eliminator
app :: Term Trivial v -> UniHSConstructor Trivial v -> Term Trivial v -> Term Trivial v
app eliminee tyEliminee arg = elim eliminee tyEliminee $ App arg

----------------------------------------------

-- | @Nat : Set = Nat@
valNat :: Entry Trivial Void
valNat = val NonOp "Nat" $
  Telescoped (
    ValRHS
      (hs2term NatType)
      (hs2type $ UniHS TrivMode)
  )

-- | @suc {n : Nat} : Nat = suc n@
valSuc :: Entry Trivial Void
valSuc = val NonOp "suc" $
  segEx NonOp "n" (hs2type NatType) :|-
  Telescoped (
    ValRHS
      (Expr2 $ TermCons $ ConsSuc $ var 0)
      (hs2type NatType)
  )

{- | @indNat {C : Nat -> Set} {cz : C 0} {cs : {n : Nat} -> C n -> C (suc n)} {n0 : Nat} : C n
        = indNat (n > C n) cz (n > ihyp > cs n ihyp) n0@
-}
-- TODO types of cz and cs and rhs need to be lifted to a higher universe
valIndNat :: Entry Trivial Void
valIndNat = val NonOp "indNat" $
  segEx NonOp "C" {- var 0 -} (hs2type $ tyMotive) :|-
  segEx NonOp "cz" {- var 1 -} (tyCZ) :|-
  segEx NonOp "cs" {- var 2 -} (hs2type $ tyCS) :|-
  segEx NonOp "n*" {- var 3 -} (hs2type NatType) :|-
  Telescoped (
    ValRHS
      (elim (var 3) NatType $ ElimDep
        (nbind NonOp "n" {- var 4 -} $ appMotive (var 4))
        (ElimNat
          (var 1)
          (nbind NonOp "n" {- var 4 -} $ nbind NonOp "ihyp" {- var 5 -} $
            app
              (app (var 2) (tyCS) (var 4))
              (tyCS' (var 4))
              (var 5)
          )
        )
      )
      (appMotive (var 3))
  )
  where
    tyMotive :: DeBruijnLevel v => UniHSConstructor Trivial v
    tyMotive = (segEx NonOp "n" $ hs2type NatType) `arrow` (hs2type $ UniHS TrivMode)
    appMotive :: DeBruijnLevel v => Term Trivial v -> Type Trivial v
    appMotive arg = Type $ app (var 0) tyMotive arg
    tyCZ :: DeBruijnLevel v => Type Trivial v
    tyCZ = appMotive $ Expr2 $ TermCons $ ConsZero
    tyCS' :: DeBruijnLevel v => Term Trivial v -> UniHSConstructor Trivial v
    tyCS' n = (segEx NonOp "ihyp" $ appMotive n)
                     `arrow` (appMotive $ Expr2 $ TermCons $ ConsSuc $ n)
    tyCS :: DeBruijnLevel v => UniHSConstructor Trivial v
    tyCS = pi (segEx NonOp "n" $ hs2type NatType) (hs2type $ tyCS' $ Var2 $ VarLast)

{- | @UniHS : UniHS = UniHS @
-}
valUniHS :: Entry Trivial Void
valUniHS = val NonOp "UniHS" $
  Telescoped (
    ValRHS
      (hs2term $ UniHS TrivMode)
      (hs2type $ UniHS TrivMode)
  )

-- | @Unit : Set = Unit@
valUnitType :: Entry Trivial Void
valUnitType = val NonOp "Unit" $
  Telescoped (
    ValRHS
      (hs2term UnitType)
      (hs2type $ UniHS TrivMode)
  )

-- | @unit : Unit = unit@
valUnitTerm :: Entry Trivial Void
valUnitTerm = val NonOp "unit" $ Telescoped $ ValRHS (Expr2 $ TermCons $ ConsUnit) (hs2type UnitType)

{-
-- | @Box {X : UniHS} : UniHS l = Box {x : X}@
valBoxType :: Entry Trivial Void
valBoxType = val NonOp "Box" $
  segEx NonOp "X" {- var 0 -} (hs2type $ UniHS TrivMode) :|-
  Telescoped (
    ValRHS
      (hs2term $ BoxType $ segEx NonOp "x" $ Type $ var 0)
      (hs2type $ UniHS TrivMode)
  )

-- | @box {~ | X : UniHS} {x : X} : Box X = box x@
valBoxTerm :: Entry Trivial Void
valBoxTerm = val NonOp "box" $
  segIm NonOp "X" {- var 0 -} (hs2type $ UniHS TrivMode) :|-
  segEx NonOp "x" {- var 1 -} (Type $ var 0) :|-
  Telescoped (
    ValRHS
      (Expr2 $ TermCons $ ConsBox boxSeg $ var 1)
      (hs2type $ BoxType $ boxSeg)
  )
  where boxSeg :: DeBruijnLevel v => Segment Type Trivial v
        boxSeg = segEx NonOp "x" $ Type $ var 0
-}

{-| indBox
      {X : Set}
      {C : Box X -> Set}
      {cbox : {x : X} -> C (box x)}
      {b0 : Box X} : C b0
        = indBox (b > C b) (x > cbox x) b0
-}
valIndBox :: Entry Trivial Void
valIndBox = val NonOp "indBox" $
  segEx NonOp "X"  {- var 0 -} (hs2type $ UniHS TrivMode) :|-
  segEx NonOp "C"  {- var 1 -} (hs2type tyMotive) :|-
  segEx NonOp "cbox" {- var 2 -} (hs2type $ tyCBox) :|-
  segEx NonOp "b*" {- var 3 -} (hs2type $ BoxType $ boxSeg) :|-
  Telescoped (
    ValRHS
      (elim
        (var 3)
        (BoxType $ boxSeg)
      $ ElimDep
        (nbind NonOp "b" {- var 4 -} $ appMotive $ var 4)
      $ ElimBox
        (nbind NonOp "x" {- var 4 -} $ app (var 2) tyCBox (var 4))
      )
      (appMotive $ var 3)
  )
  where
    boxSeg :: DeBruijnLevel v => Segment Type Trivial v
    boxSeg = segEx NonOp "x" $ Type $ var 0
    tyMotive :: DeBruijnLevel v => UniHSConstructor Trivial v
    tyMotive = (segEx NonOp "b" (hs2type $ BoxType $ boxSeg)) `arrow` (hs2type $ UniHS TrivMode)
    appMotive :: DeBruijnLevel v => Term Trivial v -> Type Trivial v
    appMotive arg = Type $ app (var 1) tyMotive arg
    tyCBox :: DeBruijnLevel v => UniHSConstructor Trivial v
    tyCBox = pi (segEx NonOp "x" (Type $ var 0)) $ appMotive $ Expr2 $ TermCons $ ConsBox boxSeg $ Var2 $ VarLast

{-| _, 
      {~ | A : Set}
      {~ | B : A -> Set}
      {x : A}
      {y : B x}
      : {x : A} >< B x
      = x , y
-}
valPair :: Entry Trivial Void
valPair = val Op "," $
  segIm NonOp "A" {- var 0 -} (hs2type $ UniHS TrivMode) :|-
  segIm NonOp "B" {- var 1 -} (hs2type $ tyCod) :|-
  segEx NonOp "x" {- var 2 -} (Type $ var 0) :|-
  segEx NonOp "y" {- var 3 -} (appCod $ var 2) :|-
  Telescoped (
    ValRHS
      (Expr2 $ TermCons $ Pair (Binding segA $ appCod $ Var2 VarLast) (var 2) (var 3))
      (hs2type $ sigma segA {- var 4 -} (appCod $ var 4))
  )
  where
    segA :: DeBruijnLevel v => Segment Type Trivial v
    segA = segEx NonOp "x" (Type $ var 0)
    tyCod :: DeBruijnLevel v => UniHSConstructor Trivial v
    tyCod = segA `arrow` (hs2type $ UniHS TrivMode)
    appCod :: DeBruijnLevel v => Term Trivial v -> Type Trivial v
    appCod arg = Type $ app (var 1) tyCod arg

{-| indPair
      {~ | A : Set}
      {~ | B : A -> Set}
      {C : ({x : A} >< B x) -> Set}
      {cpair : {x : A} {y : B x} -> C (x , y)}
      {p0 : {x : A} >< B x}
      : C p0
      = indPair (p > C) (x > y > cpair x y) p0
-}
valIndPair :: Entry Trivial Void
valIndPair = val NonOp "indPair" $
  segIm NonOp "A" {- var 0 -} (hs2type $ UniHS TrivMode) :|-
  segIm NonOp "B" {- var 1 -} (hs2type $ tyCod) :|-
  segEx NonOp "C" {- var 2 -} (hs2type $ tyMotive) :|-
  segEx NonOp "cpair" {- var 3 -} (hs2type $ tyCPair) :|-
  segEx NonOp "p*" {- var 4 -} (hs2type $ tyPair) :|-
  Telescoped (
    ValRHS
      (elim (var 4) tyPair $
       ElimDep (nbind NonOp "p" {- var 5 -} $ appMotive $ var 5) $
       ElimSigma $ nbind NonOp "x" {- var 5 -} $ nbind NonOp "y" {- var 6 -} $
       app (
         app (var 3) tyCPair (var 5)
       ) (tyCPair' (var 5)) (var 6)
      )
      (appMotive $ var 4)
  )
  where
    segA :: DeBruijnLevel v => Segment Type Trivial v
    segA = segEx NonOp "x" (Type $ var 0)
    tyCod :: DeBruijnLevel v => UniHSConstructor Trivial v
    tyCod = segA `arrow` (hs2type $ UniHS TrivMode)
    appCod :: DeBruijnLevel v => Term Trivial v -> Type Trivial v
    appCod arg = Type $ app (var 1) tyCod arg
    tyPair :: DeBruijnLevel v => UniHSConstructor Trivial v
    tyPair = sigma segA $ appCod $ Var2 $ VarLast
    tyMotive :: DeBruijnLevel v => UniHSConstructor Trivial v
    tyMotive = (segEx NonOp "p" $ hs2type tyPair) `arrow` (hs2type $ UniHS TrivMode)
    appMotive :: DeBruijnLevel v => Term Trivial v -> Type Trivial v
    appMotive arg = Type $ app (var 2) tyMotive arg
    tyCPair' :: DeBruijnLevel v => Term Trivial v -> UniHSConstructor Trivial v
    tyCPair' x = pi
      (segEx NonOp "y" $ appCod $ x)
      (appMotive $ Expr2 $ TermCons $ Pair (Binding segA $ appCod $ Var2 VarLast) (VarWkn <$> x) (Var2 VarLast))
    tyCPair :: DeBruijnLevel v => UniHSConstructor Trivial v
    tyCPair = pi segA $ hs2type $ tyCPair' $ Var2 $ VarLast

-- | @Empty : Set = Empty@
valEmpty :: Entry Trivial Void
valEmpty = val NonOp "Empty" $
  Telescoped (
    ValRHS
      (hs2term EmptyType)
      (hs2type $ UniHS TrivMode)
  )

{-| @indEmpty {C : Empty -> UniHS} {e0 : Empty} : C e0 = indEmpty (e > C e) e*@
-}
valIndEmpty :: Entry Trivial Void
valIndEmpty = val NonOp "indEmpty" $
  segEx NonOp "C" {- var 0 -} (hs2type $ tyMotive) :|-
  segEx NonOp "e*" {- var 1 -} (hs2type $ EmptyType) :|-
  Telescoped (
    ValRHS
      (elim (var 1) EmptyType $
       ElimDep (nbind NonOp "e" {- var 2 -} $ appMotive $ var 2) $
       ElimEmpty
      )
      (appMotive $ var 1)
  )
  where
    tyMotive :: DeBruijnLevel v => UniHSConstructor Trivial v
    tyMotive = (segEx NonOp "e" $ hs2type EmptyType) `arrow` (hs2type $ UniHS TrivMode)
    appMotive :: DeBruijnLevel v => Term Trivial v -> Type Trivial v
    appMotive arg = Type $ app (var 0) tyMotive arg

{-| @_== {~ | A : UniHS} {aL aR : A} : UniHS = aL == .{A} aR@
-}
valEqType :: Entry Trivial Void
valEqType = val Op "==" $
  segIm NonOp "A"  {- var 0 -} (hs2type $ UniHS TrivMode) :|-
  segEx NonOp "aL" {- var 1 -} (Type $ var 0) :|-
  segEx NonOp "aR" {- var 2 -} (Type $ var 0) :|-
  Telescoped (
    ValRHS
      (hs2term $ EqType (Type $ var 0) (var 1) (var 2))
      (hs2type $ UniHS TrivMode)
    )

{-| @refl {~| A : UniHS} {~| a : A} : a == .{A} a = refl@
-}
valRefl :: Entry Trivial Void
valRefl = val NonOp "refl" $
  segIm NonOp "A" {- var 0 -} (hs2type $ UniHS TrivMode) :|-
  segIm NonOp "a" {- var 1 -} (Type $ var 0) :|-
  Telescoped (
    ValRHS
      (Expr2 $ TermCons $ ConsRefl (Type $ var 0) (var 1))
      (hs2type $ EqType (Type $ var 0) (var 1) (var 1))
  )

{-| @ind==
        {~| A : UniHS}
        {~| aL : A}
        {C : {aR : A} -> aL == aR -> UniHS}
        {crefl : C aL (refl .{A} .{aL})}
        {~| aR* : A}
        {eq* : aL == aR}
        : C aR* eq*
        = ind== (aR > eq > C) crefl eq*@
-}
valIndEq :: Entry Trivial Void
valIndEq = val NonOp "ind==" $
  segIm NonOp "A"  {- var 0 -} (hs2type $ UniHS TrivMode) :|-
  segIm NonOp "aL" {- var 1 -} (Type $ var 0) :|-
  segEx NonOp "C"  {- var 2 -} (hs2type $ tyMotive) :|-
  segEx NonOp "crefl" {- var 3 -} (appMotive (var 1) (Expr2 $ TermCons $ ConsRefl (Type $ var 0) (var 1))) :|-
  segIm NonOp "aR*" {- var 4 -} (Type $ var 0) :|-
  segEx NonOp "eq*" {- var 5 -} (hs2type $ EqType (Type $ var 0) (var 1) (var 4)) :|-
  Telescoped (
    ValRHS
      (elim (var 5) (EqType (Type $ var 0) (var 1) (var 4)) $
       ElimEq (nbind NonOp "aR" {- var 6 -} $ nbind NonOp "eq" {- var 7 -} $ appMotive (var 6) (var 7)) (var 3))
      (appMotive (var 4) (var 5))
  )
  where
    tyMotive' :: DeBruijnLevel v => Term Trivial v -> UniHSConstructor Trivial v
    tyMotive' aR = (segEx NonOp "eq" $ hs2type $ EqType (Type $ var 0) (var 1) aR) `arrow` (hs2type $ UniHS TrivMode)
    tyMotive :: DeBruijnLevel v => UniHSConstructor Trivial v
    tyMotive = pi (segEx NonOp "aR" $ Type $ var 0) (hs2type $ tyMotive' $ Var2 VarLast)
    appMotive :: DeBruijnLevel v => Term Trivial v -> Term Trivial v -> Type Trivial v
    appMotive aR eq = Type $ app (app (var 2) tyMotive aR) (tyMotive' aR) eq

{-| @funext {~| A : UniHS} {~| B : A -> UniHS} {~| f g : {x : A} -> B x} {p : {x : A} -> f x == g x} : f == g = funext p@
-}
valFunext :: Entry Trivial Void
valFunext = val NonOp "funext" $
  segIm NonOp "A" {- var 0 -} (hs2type $ UniHS TrivMode) :|-
  segIm NonOp "B" {- var 1 -} (hs2type $ tyCod) :|-
  segIm NonOp "f" {- var 2 -} (hs2type $ tyPi) :|-
  segIm NonOp "g" {- var 3 -} (hs2type $ tyPi) :|-
  segEx NonOp "p" {- var 4 -} (hs2type $ tyEqPi) :|-
  Telescoped (
    ValRHS
      (elim (var 4) tyEqPi Funext)
      (hs2type $ EqType (hs2type $ tyPi) (var 2) (var 3))
  )  
  where
    segA :: DeBruijnLevel v => Segment Type Trivial v
    segA = segEx NonOp "x" (Type $ var 0)
    tyCod :: DeBruijnLevel v => UniHSConstructor Trivial v
    tyCod = segA `arrow` (hs2type $ UniHS TrivMode)
    appCod :: DeBruijnLevel v => Term Trivial v -> Type Trivial v
    appCod arg = Type $ app (var 1) tyCod arg
    appEqCod :: DeBruijnLevel v => Term Trivial v -> Type Trivial v
    appEqCod arg = hs2type $ EqType (appCod arg) (app (var 2) tyPi arg) (app (var 3) tyPi arg)
    tyPi :: DeBruijnLevel v => UniHSConstructor Trivial v
    tyPi = pi segA (appCod (Var2 $ VarLast))
    tyEqPi :: DeBruijnLevel v => UniHSConstructor Trivial v
    tyEqPi = pi segA (appEqCod (Var2 $ VarLast))

----------------------------------------------

magicEntries :: [Entry Trivial Void]
magicEntries = 
  valNat :
  valSuc :
  valIndNat :
  valUniHS :
  valUnitType :
  valUnitTerm :
  --valBoxType :
  --valBoxTerm :
  valIndBox :
  valPair :
  valIndPair :
  valEmpty :
  valIndEmpty :
  valEqType :
  valRefl :
  valIndEq :
  valFunext :
  []

instance SysMagicContext Trivial where
  magicModule = ModuleRHS (absurd <$> (Compose $ reverse magicEntries))

-------------------------

instance Sys Trivial where
