{-# LANGUAGE UndecidableInstances #-}

module Menkar.Fine.PrettyPrint where

import Menkar.Fine.Syntax
import Menkar.Fine.Substitution
import Menkar.Fine.Context
import Menkar.Fine.Context.Variable
import qualified Menkar.Raw as Raw
import Text.PrettyPrint.Tree
import Data.Void

class Fine2Pretty mode modty f where
  fine2pretty :: ScCtx mode modty v Void -> f mode modty v -> PrettyTree String
  fine2string :: ScCtx mode modty v Void -> f mode modty v -> String
  fine2string gamma x = render (RenderState 100 "  " "    ") $ fine2pretty gamma x

---------------------------

deriving instance (Show (mode v), Show (modty v)) => Show (ModedModality mode modty v)

deriving instance (Show (mode v), Show (modty v)) => Show (ModedContramodality mode modty v)

binding2pretty :: String -> ScCtx mode modty v Void -> Binding mode modty v -> PrettyTree String
binding2pretty opstring gamma binding =
  fine2pretty gamma (binding'segment binding)
  \\\ [" " ++ opstring ++ " " ++|
       fine2pretty (gamma ::.. (VarFromCtx <$> segment2scSegment (binding'segment binding))) (binding'body binding)
      ]
instance Fine2Pretty mode modty Binding where
  fine2pretty gamma binding = binding2pretty ">" gamma binding
instance Show (Binding mode modty Void) where
  show binding = "[Binding|\n" ++ fine2string ScCtxEmpty binding ++ "\n]"

instance (Fine2Pretty mode modty Mode, Fine2Pretty mode modty Modty) =>
         Fine2Pretty mode modty TypeTerm where
  fine2pretty gamma (UniHS d lvl) =
    ribbon "UniHS " \\\ [
      fine2pretty gamma (Mode d),
      fine2pretty gamma lvl
      ]
  fine2pretty gamma (Pi binding) = binding2pretty "->" gamma binding
  fine2pretty gamma (Sigma binding) = binding2pretty "><" gamma binding
  fine2pretty gamma (EmptyType) = ribbon "Empty"
  fine2pretty gamma (UnitType) = ribbon "Unit"
instance (Fine2Pretty mode modty Mode, Fine2Pretty mode modty Modty) =>
         Show (TypeTerm mode modty Void) where
  show typeterm = "[TypeTerm|\n" ++ fine2string ScCtxEmpty typeterm ++ "\n]"
  
instance (Fine2Pretty mode modty Mode, Fine2Pretty mode modty Modty) =>
         Fine2Pretty mode modty ConstructorTerm where
  fine2pretty gamma (ConsUniHS d typeterm) =
    ribbon "withMode" \\\ [
      " " ++| fine2pretty gamma (Mode d),
      " (" ++| fine2pretty gamma typeterm |++ ")"
      ]
  fine2pretty gamma (Lam binding) = binding2pretty ">" gamma binding
  fine2pretty gamma (Pair binding tmFst tmSnd) =
    ribbon "ofType" \\\ [
      " " ++| fine2pretty gamma (Sigma binding),
      " (" ++| fine2pretty gamma tmFst |++ " , " |+| fine2pretty gamma tmSnd |++ ")"
      ]
  fine2pretty gamma ConsUnit = ribbon "unit"
instance (Fine2Pretty mode modty Mode, Fine2Pretty mode modty Modty) =>
         Show (ConstructorTerm mode modty Void) where
  show consTerm = "[ConstructorTerm|\n" ++ fine2string ScCtxEmpty consTerm ++ "\n]"

instance (Fine2Pretty mode modty Mode, Fine2Pretty mode modty Modty) =>
         Fine2Pretty mode modty SmartEliminator where
  fine2pretty gamma (SmartElimEnd argSpec) = Raw.unparse' (Raw.ElimEnd argSpec)
  fine2pretty gamma (SmartElimArg Raw.ArgSpecNext term) = ".{" ++| fine2pretty gamma term |++ "}"
  fine2pretty gamma (SmartElimArg Raw.ArgSpecExplicit term) = "(" ++| fine2pretty gamma term |++ ")"
  fine2pretty gamma (SmartElimArg (Raw.ArgSpecNamed name) term) = ".{" ++ name ++ " = " ++| fine2pretty gamma term |++ "}"
  fine2pretty gamma (SmartElimProj projSpec) = Raw.unparse' (Raw.ElimProj projSpec)
instance (Fine2Pretty mode modty Mode, Fine2Pretty mode modty Modty) =>
         Show (SmartEliminator mode modty Void) where
  show smartElim = "[SmartEliminator|\n" ++ fine2string ScCtxEmpty smartElim ++ "\n]"

elimination2pretty :: (Fine2Pretty mode modty Mode, Fine2Pretty mode modty Modty) =>
         ScCtx mode modty v Void -> PrettyTree String -> Eliminator mode modty v -> PrettyTree String
elimination2pretty gamma eliminee (ElimUnsafeResize) = "UnsafeResize (" ++| eliminee |++ ")"
elimination2pretty gamma eliminee (App piBinding arg) = 
    ribbon "(ofType" \\\ [
      " (" ++| fine2pretty gamma (Pi piBinding) |++ ")",
      " (" ++| eliminee |++ ")"
      ] ///
    ribbon ")" \\\
      [
      " .{" ++| fine2pretty gamma arg |++ "}"
      ]
elimination2pretty gamma eliminee (ElimPair sigmaBinding motive clause) = _
elimination2pretty gamma eliminee eliminator = _elimination2pretty
-- show eliminator

instance (Fine2Pretty mode modty Mode, Fine2Pretty mode modty Modty) =>
         Fine2Pretty mode modty Type where
  fine2pretty gamma (Type t) = fine2pretty gamma t
deriving instance (Fine2Pretty mode modty Mode, Fine2Pretty mode modty Modty) => Show (Type mode modty v)

instance (Fine2Pretty mode modty Mode, Fine2Pretty mode modty Modty) =>
         Fine2Pretty mode modty TermNV where
  fine2pretty gamma (TermCons consTerm) = fine2pretty gamma consTerm
  fine2pretty gamma (TermElim mod eliminee eliminator) = _elimination
  fine2pretty gamma t = _termNV




instance Fine2Pretty mode modty (Expr3 TermNV) where
  fine2pretty gamma t = _term
instance Show (Term mode modty v) where
  show t = _showterm

instance Fine2Pretty mode modty (Telescoped ty rhs) where
  fine2pretty gamma telescoped = _telescoped
