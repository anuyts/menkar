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
import Data.Functor.Const
import Control.Lens

class Fine2Pretty mode modty f where
  fine2pretty :: ScCtx mode modty v Void -> f mode modty v -> PrettyTree String
  fine2string :: ScCtx mode modty v Void -> f mode modty v -> String
  fine2string gamma x = render (RenderState 100 "  " "    ") $ fine2pretty gamma x

---------------------------

deriving instance (Show (mode v), Show (modty v)) => Show (ModedModality mode modty v)

deriving instance (Show (mode v), Show (modty v)) => Show (ModedContramodality mode modty v)

binding2pretty :: (Functor mode, Functor modty,
                  Fine2Pretty mode modty Mode, Fine2Pretty mode modty Modty, Fine2Pretty mode modty rhs) =>
                  String -> ScCtx mode modty v Void -> Binding rhs mode modty v -> PrettyTree String
binding2pretty opstring gamma binding =
  fine2pretty gamma (binding'segment binding)
  \\\ [" " ++ opstring ++ " " ++|
       fine2pretty (gamma ::.. (VarFromCtx <$> segment2scSegment (binding'segment binding))) (binding'body binding)
      ]
instance (Functor mode, Functor modty,
         Fine2Pretty mode modty Mode, Fine2Pretty mode modty Modty, Fine2Pretty mode modty rhs) =>
         Fine2Pretty mode modty (Binding rhs) where
  fine2pretty gamma binding = binding2pretty ">" gamma binding
instance (Functor mode, Functor modty,
         Fine2Pretty mode modty Mode, Fine2Pretty mode modty Modty, Fine2Pretty mode modty rhs) =>
         Show (Binding rhs mode modty Void) where
  show binding = "[Binding|\n" ++ fine2string ScCtxEmpty binding ++ "\n]"

instance (Functor mode, Functor modty,
         Fine2Pretty mode modty Mode, Fine2Pretty mode modty Modty) =>
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
instance (Functor mode, Functor modty,
         Fine2Pretty mode modty Mode, Fine2Pretty mode modty Modty) =>
         Show (TypeTerm mode modty Void) where
  show typeterm = "[TypeTerm|\n" ++ fine2string ScCtxEmpty typeterm ++ "\n]"
  
instance (Functor mode, Functor modty,
         Fine2Pretty mode modty Mode, Fine2Pretty mode modty Modty) =>
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
instance (Functor mode, Functor modty,
         Fine2Pretty mode modty Mode, Fine2Pretty mode modty Modty) =>
         Show (ConstructorTerm mode modty Void) where
  show consTerm = "[ConstructorTerm|\n" ++ fine2string ScCtxEmpty consTerm ++ "\n]"

instance (Functor mode, Functor modty,
         Fine2Pretty mode modty Mode, Fine2Pretty mode modty Modty) =>
         Fine2Pretty mode modty SmartEliminator where
  fine2pretty gamma (SmartElimEnd argSpec) = Raw.unparse' (Raw.ElimEnd argSpec)
  fine2pretty gamma (SmartElimArg Raw.ArgSpecNext term) = ".{" ++| fine2pretty gamma term |++ "}"
  fine2pretty gamma (SmartElimArg Raw.ArgSpecExplicit term) = "(" ++| fine2pretty gamma term |++ ")"
  fine2pretty gamma (SmartElimArg (Raw.ArgSpecNamed name) term) = ".{" ++ name ++ " = " ++| fine2pretty gamma term |++ "}"
  fine2pretty gamma (SmartElimProj projSpec) = Raw.unparse' (Raw.ElimProj projSpec)
instance (Functor mode, Functor modty,
         Fine2Pretty mode modty Mode, Fine2Pretty mode modty Modty) =>
         Show (SmartEliminator mode modty Void) where
  show smartElim = "[SmartEliminator|\n" ++ fine2string ScCtxEmpty smartElim ++ "\n]"

elimination2pretty :: (Functor mode, Functor modty,
                       Fine2Pretty mode modty Mode, Fine2Pretty mode modty Modty) =>
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
instance (Functor mode, Functor modty,
         Fine2Pretty mode modty Mode, Fine2Pretty mode modty Modty) =>
         Show (Eliminator mode modty Void) where
  show elim = "[Eliminator| x > " ++ render defaultRenderState (elimination2pretty ScCtxEmpty (ribbon "x") elim)

instance (Functor mode, Functor modty,
         Fine2Pretty mode modty Mode, Fine2Pretty mode modty Modty) =>
         Fine2Pretty mode modty Type where
  fine2pretty gamma (Type t) = fine2pretty gamma t
deriving instance (Functor mode, Functor modty,
                   Fine2Pretty mode modty Mode, Fine2Pretty mode modty Modty)
    => Show (Type mode modty Void)

instance (Functor mode, Functor modty,
         Fine2Pretty mode modty Mode, Fine2Pretty mode modty Modty) =>
         Fine2Pretty mode modty TermNV where
  fine2pretty gamma (TermCons consTerm) = fine2pretty gamma consTerm
  fine2pretty gamma (TermElim mod eliminee eliminator) = elimination2pretty gamma (fine2pretty gamma eliminee) eliminator
  fine2pretty gamma (TermMeta i (Compose depcies)) = ribbon ("?" ++ show i) \\\ ((" " ++|) . fine2pretty gamma <$> depcies)
  fine2pretty gamma (TermQName qname) = Raw.unparse' qname
  fine2pretty gamma (TermSmartElim eliminee (Compose eliminators) result) =
    "(" ++| fine2pretty gamma eliminee |++ ")"
      |+| treeGroup ((" " ++|) . fine2pretty gamma <$> eliminators)
      |++ " `yielding " |+| fine2pretty gamma result
  fine2pretty gamma (TermGoal str result) =
    "?" ++ str ++ " `yielding " ++| fine2pretty gamma result
  fine2pretty gamma (TermProblem t) = "(! " ++| fine2pretty gamma t |++ "!)"
instance (Functor mode, Functor modty,
         Fine2Pretty mode modty Mode, Fine2Pretty mode modty Modty) =>
         Show (TermNV mode modty Void) where
  show t = "[TermNV|\n" ++ fine2string ScCtxEmpty t ++ "\n]"

instance (Functor mode, Functor modty,
         Fine2Pretty mode modty Mode, Fine2Pretty mode modty Modty, Fine2Pretty mode modty termNV) =>
         Fine2Pretty mode modty (Expr3 termNV) where
  fine2pretty gamma (Var3 v) = fromMaybe (ribbon "_") $ Raw.unparse' <$> scGetName gamma v
  fine2pretty gamma (Expr3 t) = fine2pretty gamma t
instance (Functor mode, Functor modty,
         Fine2Pretty mode modty Mode, Fine2Pretty mode modty Modty, Fine2Pretty mode modty termNV) =>
         Show (Expr3 termNV mode modty Void) where
  show e = "[Expr3|\n" ++ fine2string ScCtxEmpty e ++ "\n]"

----------------------

instance (Functor mode, Functor modty,
         Fine2Pretty mode modty Mode, Fine2Pretty mode modty Modty) =>
         Fine2Pretty mode modty Annotation where
  fine2pretty gamma (AnnotMode d) = "mode " ++| fine2pretty gamma (Mode d)
  fine2pretty gamma (AnnotModality mu) = "mode " ++| fine2pretty gamma (Modty mu)
  fine2pretty gamma (AnnotImplicit) = ribbon "~"
instance (Functor mode, Functor modty,
         Fine2Pretty mode modty Mode, Fine2Pretty mode modty Modty) =>
         Show (Annotation mode modty Void) where
  show annot = "[Annotation|\n" ++ fine2string ScCtxEmpty annot ++ "\n]"

instance (Functor mode, Functor modty,
         Fine2Pretty mode modty Mode, Fine2Pretty mode modty Modty) =>
         Fine2Pretty mode modty Plicity where
  fine2pretty gamma Explicit = ribbonEmpty
  fine2pretty gamma Implicit = ribbon "~"
  fine2pretty gamma (Resolves t) = "resolves " ++| fine2pretty gamma t
instance (Functor mode, Functor modty,
         Fine2Pretty mode modty Mode, Fine2Pretty mode modty Modty) =>
         Show (Plicity mode modty Void) where
  show plic = "[Plicity|\n" ++ fine2string ScCtxEmpty plic ++ "\n]"

declName2pretty :: DeclName declSort -> PrettyTree String
declName2pretty (DeclNameVal name) = Raw.unparse' name
declName2pretty (DeclNameModule str) = ribbon str
declName2pretty (DeclNameSegment maybeName) =  fromMaybe (ribbon "_") $ Raw.unparse' <$> maybeName
instance Show (DeclName declSort) where
  show declName = "[DeclName|\n" ++ render defaultRenderState (declName2pretty declName) ++ "\n]"

telescope2pretties :: (Functor mode, Functor modty, Functor (ty mode modty),
         Fine2Pretty mode modty Mode, Fine2Pretty mode modty Modty, Fine2Pretty mode modty ty) =>
         ScCtx mode modty v Void -> Telescope ty mode modty v -> [PrettyTree String]
telescope2pretties gamma (Telescoped Unit3) = []
telescope2pretties gamma (seg :|- telescope) =
  (fine2pretty gamma seg) : telescope2pretties (gamma ::.. (VarFromCtx <$> segment2scSegment seg)) telescope
instance (Functor mode, Functor modty, Functor (ty mode modty),
         Fine2Pretty mode modty Mode, Fine2Pretty mode modty Modty, Fine2Pretty mode modty ty) =>
         Fine2Pretty mode modty (Telescope ty) where
  fine2pretty gamma telescope = treeGroup $ telescope2pretties gamma telescope
instance (Functor mode, Functor modty, Functor (ty mode modty),
         Fine2Pretty mode modty Mode, Fine2Pretty mode modty Modty, Fine2Pretty mode modty ty) =>
         Show (Telescope ty mode modty Void) where
  show theta = "[Telescope|\n" ++ fine2string ScCtxEmpty theta ++ "\n]"

tdeclAnnots2pretties :: (Functor mode, Functor modty, Functor (ty mode modty),
         Fine2Pretty mode modty Mode, Fine2Pretty mode modty Modty, Fine2Pretty mode modty ty) =>
         ScCtx mode modty v Void -> TelescopedDeclaration declSort ty content mode modty v -> [PrettyTree String]
tdeclAnnots2pretties gamma tdecl =
        getConst (mapTelescopedSc (
            \ wkn gammadelta decl -> Const $ [
                fine2pretty gammadelta (_decl'plicity decl),
                "[mode " ++| fine2pretty gammadelta (Mode $ modDom $ _decl'modty decl) |++ "] ",
                "[mod " ++| fine2pretty gammadelta (Modty $ modMod $ _decl'modty decl) |++ "] "
              ]
          ) gamma tdecl)

instance (Functor mode, Functor modty, Functor (ty mode modty),
         Fine2Pretty mode modty Mode, Fine2Pretty mode modty Modty, Fine2Pretty mode modty ty) =>
         Fine2Pretty mode modty (Segment ty) where
  fine2pretty gamma seg = ribbon " {" \\\
    prettyAnnots ///
    "| " ++| (declName2pretty $ DeclNameSegment $ _segment'name seg) \\\
    telescope2pretties gamma (telescoped'telescope seg) ///
    " : " ++| prettyType |++ "}"
    where
      prettyAnnots = tdeclAnnots2pretties gamma seg
      prettyType =
        getConst (mapTelescopedSc (
            \ wkn gammadelta decl -> Const $ fine2pretty gammadelta (_decl'content decl)
          ) gamma seg)
instance (Functor mode, Functor modty, Functor (ty mode modty),
         Fine2Pretty mode modty Mode, Fine2Pretty mode modty Modty, Fine2Pretty mode modty ty) =>
         Show (Segment ty mode modty Void) where
  show seg = "[Segment|\n" ++ fine2string ScCtxEmpty seg ++ "\n]"

instance (Functor mode, Functor modty,
         Fine2Pretty mode modty Mode, Fine2Pretty mode modty Modty) =>
         Fine2Pretty mode modty ValRHS where
  fine2pretty gamma (ValRHS tm ty) = treeGroup [
      " : " ++| fine2pretty gamma ty,
      " = " ++| fine2pretty gamma tm
    ]
instance (Functor mode, Functor modty,
         Fine2Pretty mode modty Mode, Fine2Pretty mode modty Modty) =>
         Show (ValRHS mode modty Void) where
  show valRHS = "[ValRHS|\n" ++ fine2string ScCtxEmpty valRHS ++ "\n]"

instance (Functor mode, Functor modty,
         Fine2Pretty mode modty Mode, Fine2Pretty mode modty Modty) =>
         Fine2Pretty mode modty Val where
  fine2pretty gamma val =
    ribbon "val "
    \\\ prettyAnnots
    /// (declName2pretty $ _tdecl'name val)
    \\\ telescope2pretties gamma (telescoped'telescope val)
    /// prettyValRHS
    where
      prettyAnnots = tdeclAnnots2pretties gamma val
      prettyValRHS = 
        getConst (mapTelescopedSc (
            \ wkn gammadelta decl -> Const $ fine2pretty gammadelta (_decl'content decl)
          ) gamma val)
instance (Functor mode, Functor modty,
         Fine2Pretty mode modty Mode, Fine2Pretty mode modty Modty) =>
         Show (Val mode modty Void) where
  show val = "[Val|\n" ++ fine2string ScCtxEmpty val ++ "\n]"
        
instance (Functor mode, Functor modty,
         Fine2Pretty mode modty Mode, Fine2Pretty mode modty Modty) =>
         Fine2Pretty mode modty ModuleRHS where
  fine2pretty gamma moduleRHS = ribbon " where {"
    \\\ ((fine2pretty (gamma ::<...> (VarFromCtx <$> moduleRHS)) <$> (reverse $ view moduleRHS'entries moduleRHS))
          >>= (\ entry -> [entry, ribbon "        "]))
    /// ribbon "}"
instance (Functor mode, Functor modty,
         Fine2Pretty mode modty Mode, Fine2Pretty mode modty Modty) =>
         Show (ModuleRHS mode modty Void) where
  show moduleRHS = "[ModuleRHS|\n" ++ fine2string ScCtxEmpty moduleRHS ++ "\n]"

instance (Functor mode, Functor modty,
         Fine2Pretty mode modty Mode, Fine2Pretty mode modty Modty) =>
         Fine2Pretty mode modty Module where
  fine2pretty gamma modul =
    ribbon "module "
    \\\ prettyAnnots
    /// (declName2pretty $ _tdecl'name modul)
    \\\ telescope2pretties gamma (telescoped'telescope modul)
    /// prettyValRHS
    where
      prettyAnnots = tdeclAnnots2pretties gamma modul
      prettyValRHS = 
        getConst (mapTelescopedSc (
            \ wkn gammadelta decl -> Const $ fine2pretty gammadelta (_decl'content decl)
          ) gamma modul)
instance (Functor mode, Functor modty,
         Fine2Pretty mode modty Mode, Fine2Pretty mode modty Modty) =>
         Show (Module mode modty Void) where
  show modul = "[Module|\n" ++ fine2string ScCtxEmpty modul ++ "\n]"

instance (Functor mode, Functor modty,
         Fine2Pretty mode modty Mode, Fine2Pretty mode modty Modty) =>
         Fine2Pretty mode modty Entry where
  fine2pretty gamma (EntryVal val) = fine2pretty gamma val
  fine2pretty gamma (EntryModule modul) = fine2pretty gamma modul
instance (Functor mode, Functor modty,
         Fine2Pretty mode modty Mode, Fine2Pretty mode modty Modty) =>
         Show (Entry mode modty Void) where
  show entry = "[Entry|\n" ++ fine2string ScCtxEmpty entry ++ "\n]"
