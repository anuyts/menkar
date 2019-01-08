module Menkar.Fine.Multimode.Trivial.MagicContext where

import Menkar.Basic.Syntax
import Menkar.Fine.Syntax
import Menkar.Fine.Context
--import Menkar.Fine.Multimode
import Menkar.Fine.Multimode.Trivial.Trivial
import Menkar.Basic.Context

import Data.Void
import Data.Functor.Compose
import GHC.Generics (U1 (..))

magicEntries :: [Entry U1 U1 Void]
magicEntries = [
    {- Natural numbers
       Nat {~ | l : Nat} : Set l = Nat
    -}
    EntryVal $ Declaration
      (DeclNameVal $ Name NonOp "Nat")
      trivModedModality
      Explicit
      $ Declaration
          (DeclNameSegment $ Just $ Name NonOp "lvl")
          trivModedModality
          Implicit
          (Type $ Expr3 $ TermCons $ ConsUniHS $ NatType)
        :|-
          Telescoped (
            ValRHS
              (Expr3 $ TermCons $ ConsUniHS $ NatType)
              (Type $ Expr3 $ TermCons $ ConsUniHS $ UniHS U1 $ Var3 VarLast)
          ),

    {- Successor
       suc {n : Nat} : Nat = suc n
    -}
    EntryVal $ Declaration
      (DeclNameVal $ Name NonOp "suc")
      trivModedModality
      Explicit
      $ Declaration
          (DeclNameSegment $ Just $ Name NonOp "n")
          trivModedModality
          Explicit
          (Type $ Expr3 $ TermCons $ ConsUniHS $ NatType)
        :|-
          Telescoped (
            ValRHS
              (Expr3 $ TermCons $ ConsSuc $ Var3 $ VarLast)
              (Type $ Expr3 $ TermCons $ ConsUniHS $ NatType)
          ),

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
