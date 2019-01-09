module Menkar.Fine.Multimode.Trivial.MagicContext where

import Prelude hiding (pi)

import Menkar.Basic.Syntax
import Menkar.Fine.Syntax
import Menkar.Fine.Context
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
  segIm NonOp "lvl" (hs2type NatType) :|-
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

----------------------------------------------

magicEntries :: [Entry U1 U1 Void]
magicEntries = [
    valNat,
    valSuc,
    valIndNat, -- doesn't type-check
    valUniHS
  ]

magicContext :: Ctx Type U1 U1 (VarInModule Void) Void
magicContext = CtxEmpty U1 :<...> ModuleRHS (absurd <$> (Compose $ reverse magicEntries))
