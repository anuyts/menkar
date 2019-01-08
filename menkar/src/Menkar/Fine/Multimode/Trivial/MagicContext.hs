module Menkar.Fine.Multimode.Trivial.MagicContext where

import Menkar.Basic.Syntax
import Menkar.Fine.Syntax
import Menkar.Fine.Context
--import Menkar.Fine.Multimode
import Menkar.Fine.Multimode.Trivial.Trivial

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
          )
  ]

magicContext :: Ctx Type U1 U1 (VarInModule Void) Void
magicContext = CtxEmpty U1 :<...> ModuleRHS (absurd <$> (Compose $ reverse magicEntries))
