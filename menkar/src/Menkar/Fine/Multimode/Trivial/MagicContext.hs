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
import GHC.Stack

-- | These are de Bruijn LEVELS, not INDICES!!!
var :: (HasCallStack, DeBruijnLevel v) => Nat -> Term U1 U1 v
var n = Var3 $ fromMaybe unreachable $ forDeBruijnLevel Proxy n

val :: Opness -> String -> Telescoped Type ValRHS U1 U1 v -> Entry U1 U1 v
val op str rhs = EntryVal $ Declaration
  (DeclNameVal $ Name op str)
  trivModedModality
  Explicit
  rhs

pi :: Segment Type U1 U1 v -> Type U1 U1 (VarExt v) -> UniHSConstructor U1 U1 v
pi aSeg cod = Pi $ Binding aSeg (unType cod)
sigma :: Segment Type U1 U1 v -> Type U1 U1 (VarExt v) -> UniHSConstructor U1 U1 v
sigma aSeg cod = Sigma $ Binding aSeg (unType cod)
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

-- | @Nat : Set = Nat@
valNat :: Entry U1 U1 Void
valNat = val NonOp "Nat" $
  Telescoped (
    ValRHS
      (hs2term NatType)
      (hs2type $ UniHS U1)
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

{- | @indNat {C : Nat -> Set} {cz : C 0} {cs : {n : Nat} -> C n -> C (suc n)} {n0 : Nat} : C n
        = indNat (n > C n) cz (n > ihyp > cs n ihyp) n0@
-}
-- TODO types of cz and cs and rhs need to be lifted to a higher universe
valIndNat :: Entry U1 U1 Void
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
    tyMotive :: DeBruijnLevel v => UniHSConstructor U1 U1 v
    tyMotive = (segEx NonOp "n" $ hs2type NatType) `arrow` (hs2type $ UniHS U1)
    appMotive :: DeBruijnLevel v => Term U1 U1 v -> Type U1 U1 v
    appMotive arg = Type $ app (var 0) tyMotive arg
    tyCZ :: DeBruijnLevel v => Type U1 U1 v
    tyCZ = appMotive $ Expr3 $ TermCons $ ConsZero
    tyCS' :: DeBruijnLevel v => Term U1 U1 v -> UniHSConstructor U1 U1 v
    tyCS' n = (segEx NonOp "ihyp" $ appMotive n)
                     `arrow` (appMotive $ Expr3 $ TermCons $ ConsSuc $ n)
    tyCS :: DeBruijnLevel v => UniHSConstructor U1 U1 v
    tyCS = pi (segEx NonOp "n" $ hs2type NatType) (hs2type $ tyCS' $ Var3 $ VarLast)

{- | @UniHS : UniHS = UniHS @
-}
valUniHS :: Entry U1 U1 Void
valUniHS = val NonOp "UniHS" $
  Telescoped (
    ValRHS
      (hs2term $ UniHS U1)
      (hs2type $ UniHS U1)
  )

-- | @Unit : Set = Unit@
valUnitType :: Entry U1 U1 Void
valUnitType = val NonOp "Unit" $
  Telescoped (
    ValRHS
      (hs2term UnitType)
      (hs2type $ UniHS U1)
  )

-- | @unit : Unit = unit@
valUnitTerm :: Entry U1 U1 Void
valUnitTerm = val NonOp "unit" $ Telescoped $ ValRHS (Expr3 $ TermCons $ ConsUnit) (hs2type UnitType)

-- | @Box {X : UniHS} : UniHS l = Box {x : X}@
valBoxType :: Entry U1 U1 Void
valBoxType = val NonOp "Box" $
  segEx NonOp "X" {- var 0 -} (hs2type $ UniHS U1) :|-
  Telescoped (
    ValRHS
      (hs2term $ BoxType $ segEx NonOp "x" $ Type $ var 0)
      (hs2type $ UniHS U1)
  )

-- | @box {~ | X : UniHS} {x : X} : Box X = box x@
valBoxTerm :: Entry U1 U1 Void
valBoxTerm = val NonOp "box" $
  segIm NonOp "X" {- var 0 -} (hs2type $ UniHS U1) :|-
  segEx NonOp "x" {- var 1 -} (Type $ var 0) :|-
  Telescoped (
    ValRHS
      (Expr3 $ TermCons $ ConsBox boxSeg $ var 1)
      (hs2type $ BoxType $ boxSeg)
  )
  where boxSeg :: DeBruijnLevel v => Segment Type U1 U1 v
        boxSeg = segEx NonOp "x" $ Type $ var 0

{-| indBox
      {X : Set}
      {C : Box X -> Set}
      {cbox : {x : X} -> C (box x)}
      {b0 : Box X} : C b0
        = indBox (b > C b) (x > cbox x) b0
-}
valIndBox :: Entry U1 U1 Void
valIndBox = val NonOp "indBox" $
  segEx NonOp "X"  {- var 0 -} (hs2type $ UniHS U1) :|-
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
    boxSeg :: DeBruijnLevel v => Segment Type U1 U1 v
    boxSeg = segEx NonOp "x" $ Type $ var 0
    tyMotive :: DeBruijnLevel v => UniHSConstructor U1 U1 v
    tyMotive = (segEx NonOp "b" (hs2type $ BoxType $ boxSeg)) `arrow` (hs2type $ UniHS U1)
    appMotive :: DeBruijnLevel v => Term U1 U1 v -> Type U1 U1 v
    appMotive arg = Type $ app (var 1) tyMotive arg
    tyCBox :: DeBruijnLevel v => UniHSConstructor U1 U1 v
    tyCBox = pi (segEx NonOp "x" (Type $ var 0)) $ appMotive $ Expr3 $ TermCons $ ConsBox boxSeg $ Var3 $ VarLast

{-| _, 
      {~ | A : Set}
      {~ | B : A -> Set}
      {x : A}
      {y : B x}
      : {x : A} >< B x
      = x , y
-}
valPair :: Entry U1 U1 Void
valPair = val Op "," $
  segIm NonOp "A" {- var 0 -} (hs2type $ UniHS U1) :|-
  segIm NonOp "B" {- var 1 -} (hs2type $ tyCod) :|-
  segEx NonOp "x" {- var 2 -} (Type $ var 0) :|-
  segEx NonOp "y" {- var 3 -} (appCod $ var 2) :|-
  Telescoped (
    ValRHS
      (Expr3 $ TermCons $ Pair (Binding segA $ unType $ appCod $ Var3 VarLast) (var 2) (var 3))
      (hs2type $ sigma segA (appCod $ var 4))
  )
  where
    segA :: DeBruijnLevel v => Segment Type U1 U1 v
    segA = segEx NonOp "x" (Type $ var 0)
    tyCod :: DeBruijnLevel v => UniHSConstructor U1 U1 v
    tyCod = segA `arrow` (hs2type $ UniHS U1)
    appCod :: DeBruijnLevel v => Term U1 U1 v -> Type U1 U1 v
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
valIndPair :: Entry U1 U1 Void
valIndPair = val NonOp "indPair" $
  segIm NonOp "A" {- var 0 -} (hs2type $ UniHS U1) :|-
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
    segA :: DeBruijnLevel v => Segment Type U1 U1 v
    segA = segEx NonOp "x" (Type $ var 0)
    tyCod :: DeBruijnLevel v => UniHSConstructor U1 U1 v
    tyCod = segA `arrow` (hs2type $ UniHS U1)
    appCod :: DeBruijnLevel v => Term U1 U1 v -> Type U1 U1 v
    appCod arg = Type $ app (var 1) tyCod arg
    tyPair :: DeBruijnLevel v => UniHSConstructor U1 U1 v
    tyPair = sigma segA $ appCod $ Var3 $ VarLast
    tyMotive :: DeBruijnLevel v => UniHSConstructor U1 U1 v
    tyMotive = (segEx NonOp "p" $ hs2type tyPair) `arrow` (hs2type $ UniHS U1)
    appMotive :: DeBruijnLevel v => Term U1 U1 v -> Type U1 U1 v
    appMotive arg = Type $ app (var 2) tyMotive arg
    tyCPair' :: DeBruijnLevel v => Term U1 U1 v -> UniHSConstructor U1 U1 v
    tyCPair' x = pi
      (segEx NonOp "y" $ appCod $ x)
      (appMotive $ Expr3 $ TermCons $ Pair (Binding segA $ unType $ appCod $ Var3 VarLast) (VarWkn <$> x) (Var3 VarLast))
    tyCPair :: DeBruijnLevel v => UniHSConstructor U1 U1 v
    tyCPair = pi segA $ hs2type $ tyCPair' $ Var3 $ VarLast

-- | @Empty : Set = Empty@
valEmpty :: Entry U1 U1 Void
valEmpty = val NonOp "Empty" $
  Telescoped (
    ValRHS
      (hs2term EmptyType)
      (hs2type $ UniHS U1)
  )

{-| @indEmpty {C : Empty -> UniHS} {e0 : Empty} : C e0 = indEmpty (e > C e) e*@
-}
valIndEmpty :: Entry U1 U1 Void
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
    tyMotive :: DeBruijnLevel v => UniHSConstructor U1 U1 v
    tyMotive = (segEx NonOp "e" $ hs2type EmptyType) `arrow` (hs2type $ UniHS U1)
    appMotive :: DeBruijnLevel v => Term U1 U1 v -> Type U1 U1 v
    appMotive arg = Type $ app (var 0) tyMotive arg

{-| @_== {~ | A : UniHS} {aL aR : A} : UniHS = aL == .{A} aR@
-}
valEqType :: Entry U1 U1 Void
valEqType = val Op "==" $
  segIm NonOp "A"  {- var 0 -} (hs2type $ UniHS U1) :|-
  segEx NonOp "aL" {- var 1 -} (Type $ var 0) :|-
  segEx NonOp "aR" {- var 2 -} (Type $ var 0) :|-
  Telescoped (
    ValRHS
      (hs2term $ EqType (Type $ var 0) (var 1) (var 2))
      (hs2type $ UniHS U1)
    )

{-| @refl {~| A : UniHS} {~| a : A} : a == .{A} a = refl@
-}
valRefl :: Entry U1 U1 Void
valRefl = val NonOp "refl" $
  segIm NonOp "A" {- var 0 -} (hs2type $ UniHS U1) :|-
  segIm NonOp "a" {- var 1 -} (Type $ var 0) :|-
  Telescoped (
    ValRHS
      (Expr3 $ TermCons $ ConsRefl)
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
valIndEq :: Entry U1 U1 Void
valIndEq = val NonOp "ind==" $
  segIm NonOp "A"  {- var 0 -} (hs2type $ UniHS U1) :|-
  segIm NonOp "aL" {- var 1 -} (Type $ var 0) :|-
  segEx NonOp "C"  {- var 2 -} (hs2type $ tyMotive) :|-
  segEx NonOp "crefl" {- var 3 -} (appMotive (var 1) (Expr3 $ TermCons $ ConsRefl)) :|-
  segIm NonOp "aR*" {- var 4 -} (Type $ var 0) :|-
  segEx NonOp "eq*" {- var 5 -} (hs2type $ EqType (Type $ var 0) (var 1) (var 4)) :|-
  Telescoped (
    ValRHS
      (elim (var 5) (EqType (Type $ var 0) (var 1) (var 4)) $
       ElimEq (nbind NonOp "aR" {- var 6 -} $ nbind NonOp "eq" {- var 7 -} $ appMotive (var 6) (var 7)) (var 3))
      (appMotive (var 4) (var 5))
  )
  where
    tyMotive' :: DeBruijnLevel v => Term U1 U1 v -> UniHSConstructor U1 U1 v
    tyMotive' aR = (segEx NonOp "eq" $ hs2type $ EqType (Type $ var 0) (var 1) aR) `arrow` (hs2type $ UniHS U1)
    tyMotive :: DeBruijnLevel v => UniHSConstructor U1 U1 v
    tyMotive = pi (segEx NonOp "aR" $ Type $ var 0) (hs2type $ tyMotive' $ Var3 VarLast)
    appMotive :: DeBruijnLevel v => Term U1 U1 v -> Term U1 U1 v -> Type U1 U1 v
    appMotive aR eq = Type $ app (app (var 2) tyMotive aR) (tyMotive' aR) eq

----------------------------------------------

magicEntries :: [Entry U1 U1 Void]
magicEntries = 
  valNat :
  valSuc :
  valIndNat :
  valUniHS :
  valUnitType :
  valUnitTerm :
  valBoxType :
  valBoxTerm :
  valIndBox :
  valPair :
  valIndPair :
  valEmpty :
  valIndEmpty :
  valEqType :
  valRefl :
  valIndEq :
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
