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
          (DeclNameSegment $ Nothing)
          trivModedModality
          Implicit
          (Type $ Expr3 $ TermCons $ ConsUniHS $ NatType)
        :|-
          Telescoped (
            ValRHS
              (Expr3 $ TermCons $ ConsUniHS $ NatType)
              (Type $ Expr3 $ TermCons $ ConsUniHS $ UniHS U1 $ Var3 VarLast)
          )
  ]

magicContext :: Ctx Type U1 U1 (VarInModule Void) Void
magicContext = CtxEmpty U1 :<...> ModuleRHS (absurd <$> (Compose $ reverse magicEntries))
