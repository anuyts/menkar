module Menkar.Fine.Multimode.Trivial.MagicContext where

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

seg :: Plicity U1 U1 v -> Opness -> String -> content U1 U1 v -> Segment content U1 U1 v
seg plic op str content = Declaration
  (DeclNameSegment $ Just $ Name op str)
  trivModedModality
  plic
  content
segIm = seg Implicit
segEx = seg Explicit

-- | Nat {~ | l : Nat} : Set l = Nat
valNat :: Entry U1 U1 Void
valNat = val NonOp "Nat" $
  segIm NonOp "lvl" (hs2type NatType) :|-
  Telescoped (
    ValRHS
      (hs2term NatType)
      (hs2type $ UniHS U1 $ var 0)
  )

-- | suc {n : Nat} : Nat = suc n
valSuc :: Entry U1 U1 Void
valSuc = val NonOp "suc" $
  segEx NonOp "n" (hs2type NatType) :|-
  Telescoped (
    ValRHS
      (Expr3 $ TermCons $ ConsSuc $ var 0)
      (hs2type NatType)
  )

magicEntries :: [Entry U1 U1 Void]
magicEntries = [
    valNat,
    valSuc

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
