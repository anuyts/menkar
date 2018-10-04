{-# LANGUAGE UndecidableInstances #-}

module Menkar.Fine.PrettyPrint where

import Menkar.Fine.Syntax
import Menkar.Fine.Substitution
import Menkar.Fine.Context
import Menkar.Fine.Context.Variable
import qualified Menkar.Raw as Raw
import Text.PrettyPrint.Tree
import Data.Void
import Data.Maybe
import Control.Exception.AssertFalse
import Data.Functor.Compose

class Fine2Pretty mode modty f where
  fine2pretty :: ScCtx mode modty v Void -> f mode modty v -> PrettyTree String
  fine2string :: ScCtx mode modty v Void -> f mode modty v -> String
  fine2string gamma x = render (RenderState 100 "  " "    ") $ fine2pretty gamma x

---------------------------

deriving instance (Show (mode v), Show (modty v)) => Show (ModedModality mode modty v)

deriving instance (Show (mode v), Show (modty v)) => Show (ModedContramodality mode modty v)

binding2pretty :: Fine2Pretty mode modty rhs =>
  String -> ScCtx mode modty v Void -> Binding rhs mode modty v -> PrettyTree String
binding2pretty opstring gamma binding =
  fine2pretty gamma (binding'segment binding)
  \\\ [" " ++ opstring ++ " " ++|
       fine2pretty (gamma ::.. (VarFromCtx <$> segment2scSegment (binding'segment binding))) (binding'body binding)
      ]
instance Fine2Pretty mode modty rhs => Fine2Pretty mode modty (Binding rhs) where
  fine2pretty gamma binding = binding2pretty ">" gamma binding
instance Fine2Pretty mode modty rhs => Show (Binding rhs mode modty Void) where
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
elimination2pretty gamma eliminee (ElimPair motive clause) =
  ribbon "ofType" \\\ [
    " (" ++| fine2pretty gamma (Pi motive) |++ ")",
    " (" ++ nameFst ++ " , " ++ nameSnd ++ " > " ++| fine2pretty gammaFstSnd body |++ ")",
    " (" ++| eliminee |++ ")"
    ]
    where
      nameFst = fromMaybe "_" $ Raw.unparse <$> _segment'name (binding'segment clause)
      nameSnd = fromMaybe "_" $ Raw.unparse <$> _segment'name (binding'segment $ binding'body clause)
      body = binding'body $ binding'body $ clause
      gammaFstSnd = gamma
        ::.. (VarFromCtx <$> segment2scSegment (binding'segment clause))
        ::.. (VarFromCtx <$> segment2scSegment (binding'segment (binding'body clause)))
elimination2pretty gamma eliminee (Fst sigmaBinding) = todo
elimination2pretty gamma eliminee (Snd sigmaBinding) = todo
elimination2pretty gamma eliminee (ElimEmpty motive) = 
  ribbon "ofType" \\\ [
    " (" ++| fine2pretty gamma (Pi motive) |++ ")",
    ribbon " absurd",
    " (" ++| eliminee |++ ")"
    ]
instance (Fine2Pretty mode modty Mode, Fine2Pretty mode modty Modty) =>
         Show (Eliminator mode modty Void) where
  show elim = "[Eliminator| x > " ++ render defaultRenderState (elimination2pretty ScCtxEmpty (ribbon "x") elim)

instance (Fine2Pretty mode modty Mode, Fine2Pretty mode modty Modty) =>
         Fine2Pretty mode modty Type where
  fine2pretty gamma (Type t) = fine2pretty gamma t
deriving instance (Fine2Pretty mode modty Mode, Fine2Pretty mode modty Modty) => Show (Type mode modty Void)

instance (Fine2Pretty mode modty Mode, Fine2Pretty mode modty Modty) =>
         Fine2Pretty mode modty TermNV where
  fine2pretty gamma (TermCons consTerm) = fine2pretty gamma consTerm
  fine2pretty gamma (TermElim mod eliminee eliminator) = elimination2pretty gamma (fine2pretty gamma eliminee) eliminator
  fine2pretty gamma (TermMeta i (Compose depcies)) = ribbon ("?" ++ show i) \\\ (fine2pretty gamma <$> depcies)
instance (Fine2Pretty mode modty Mode, Fine2Pretty mode modty Modty) =>
         Show (TermNV mode modty Void) where
  show t = fine2string ScCtxEmpty t

instance (Fine2Pretty mode modty Mode, Fine2Pretty mode modty Modty, Fine2Pretty mode modty termNV) =>
         Fine2Pretty mode modty (Expr3 termNV) where
  fine2pretty gamma (Var3 v) = ribbon $ fromMaybe "_" $ Raw.unparse <$> scGetName gamma v
  fine2pretty gamma (Expr3 t) = fine2pretty gamma t
instance (Fine2Pretty mode modty Mode, Fine2Pretty mode modty Modty, Fine2Pretty mode modty termNV) =>
         Show (Expr3 termNV mode modty Void) where
  show e = fine2string ScCtxEmpty e



instance Fine2Pretty mode modty (Telescoped ty rhs) where
  fine2pretty gamma telescoped = _telescoped
