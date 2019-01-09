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
valIndNat :: Entry U1 U1 Void
valIndNat = val NonOp "indNat" $
  segIm NonOp "l" (hs2type NatType) :|-
  segEx NonOp "C" (hs2type $ tyMotive $ var 0) :|-
  segEx NonOp "cz" (tyCZ (var 1) (var 0)) :|-
  segEx NonOp "cs" (hs2type $ tyCS (var 2) (var 1)) :|-
  segEx NonOp "n0" (hs2type NatType) :|-
  Telescoped (
    ValRHS
      (elim (var 0) NatType $ ElimDep
        (nbind NonOp "n" $ appMotive (var 5) (var 4) (var 0))
        (ElimNat
          (var 2)
          (nbind NonOp "n" $ nbind NonOp "ihyp" $
            app
              (app
                (var 3)
                (tyCS (var 6) (var 5))
                (var 1)
              )
              (tyCS' (var 6) (var 5) (var 1))
              (var 0)
          )
        )
      )
      (appMotive (var 4) (var 3) (var 0))
  )
  where
    tyMotive :: Term U1 U1 v -> UniHSConstructor U1 U1 v
    tyMotive l = (segEx NonOp "n" $ hs2type NatType) `arrow` (hs2type $ UniHS U1 l)
    appMotive :: Term U1 U1 v -> Term U1 U1 v -> Term U1 U1 v -> Type U1 U1 v
    appMotive l motive arg = Type $ app motive (tyMotive l) arg
    tyCZ :: Term U1 U1 v -> Term U1 U1 v -> Type U1 U1 v
    tyCZ l motive = appMotive l motive $ Expr3 $ TermCons $ ConsZero
    tyCS' :: Term U1 U1 v -> Term U1 U1 v -> Term U1 U1 v -> UniHSConstructor U1 U1 v
    tyCS' l motive n = (segEx NonOp "ihyp" $ appMotive l motive n)
                     `arrow` (appMotive l motive $ Expr3 $ TermCons $ ConsSuc $ n)
    tyCS :: DeBruijnLevel v => Term U1 U1 v -> Term U1 U1 v -> UniHSConstructor U1 U1 v
    tyCS l motive = pi (segEx NonOp "n" $ hs2type NatType) (hs2type $ tyCS' (VarWkn <$> l) (VarWkn <$> motive) $ var 0)

magicEntries :: [Entry U1 U1 Void]
magicEntries = [
    valNat,
    valSuc,
    valIndNat

    {-
    {- indNat {~ | l : Nat} {C : {n : Nat} -> Set l} {cz : C 0} {cs : {n : Nat} -> C n -> C (suc n)} {n : Nat} : C n
         = indNat (n > C n) cz (n > ihyp > cs n ihyp) n
    -}
    EntryVal $ Declaration
      (DeclNameVal $ Name NonOp "indNat")
      trivModedModality
      Explicit
      $ Declaration
          (DeclNameSegment $ Just $ Name NonOp "l")
          trivModedModality
          Implicit
          (Type $ Expr3 $ TermCons $ ConsUniHS $ NatType)
        :|-
        Declaration
          (DeclNameSegment $ Just $ Name NonOp "C")
          trivModedModality
          Explicit
          (Type $ Expr3 $ TermCons $ ConsUniHS $ tyNatMotive)
        :|-
        Declaration
          (DeclNameSegment $ Just $ Name NonOp "cz")
          trivModedModality
          Explicit
          (Type $ appMotive (Var3 VarLast) $ Expr3 $ TermCons $ ConsZero)
        :|-
        Declaration
          (DeclNameSegment $ Just $ Name NonOp "cs")
          trivModedModality
          Explicit
          (Type $ Expr3 $ TermCons $ ConsUniHS $ Pi $ Binding
            (Declaration
              (DeclNameSegment $ Just $ Name NonOp "n")
              trivModedModality
              Explicit
              (Type $ Expr3 $ TermCons $ ConsUniHS $ NatType)
            )
            (Expr3 $ TermCons $ ConsUniHS $ Pi $ Binding
              (Declaration
                (DeclNameSegment $ Just $ Name NonOp "ihyp")
                trivModedModality
                Explicit
                (Type $ appMotive (Var3 $ VarWkn $ VarWkn $ VarLast) $ Var3 $ VarLast)
              )
              (appMotive (Var3 $ VarWkn $ VarWkn $ VarWkn $ VarLast) $ Expr3 $ TermCons $ ConsSuc $ Var3 $ VarWkn $ VarLast)
            )
          )
        :|-
        Declaration
          (DeclNameSegment $ Just $ Name NonOp "n")
          trivModedModality
          Implicit
          (Type $ Expr3 $ TermCons $ ConsUniHS $ NatType)
        :|- Telescoped (
            ValRHS
              (Expr3 $ TermElim
                trivModedModality
                (Var3 $ VarLast)
                (NatType)
                (ElimDep
                  (NamedBinding (Just $ Name NonOp "n") $
                    Type $ appMotive (Var3 $ VarWkn $ VarWkn $ VarWkn $ VarLast) $ Var3 VarLast
                  )
                  (ElimNat
                    (Var3 $ VarWkn $ VarWkn $ VarLast)
                    (NamedBinding (Just $ Name NonOp "n") $
                     NamedBinding (Just $ Name NonOp "ihyp") $
                     Expr3 $ TermElim
                       trivModedModality
                       (Expr3 $ TermElim
                         trivModedModality
                         (Var3 $ VarWkn $ VarWkn $ VarWkn $ VarLast)
                         _
                         $ App $ Var3 $ VarWkn $ VarLast
                       )
                       _
                       $ App $ Var3 $ VarLast
                    )
                  )
                )
              )
              (Type $ appMotive (Var3 $ VarWkn $ VarWkn $ VarWkn $ VarLast) $ Var3 $ VarLast)
          )
-}
  ]
  where
    tyNatMotive = Pi $ Binding
            (Declaration
              (DeclNameSegment $ Just $ Name NonOp "n")
              trivModedModality
              Explicit
              (Type $ Expr3 $ TermCons $ ConsUniHS $ NatType)
            )
            (Expr3 $ TermCons $ ConsUniHS $ UniHS U1 $ Var3 VarLast)
    appMotive vMotive n = Expr3 $ TermElim
            trivModedModality
            vMotive
            tyNatMotive
            (App $ n)

magicContext :: Ctx Type U1 U1 (VarInModule Void) Void
magicContext = CtxEmpty U1 :<...> ModuleRHS (absurd <$> (Compose $ reverse magicEntries))
