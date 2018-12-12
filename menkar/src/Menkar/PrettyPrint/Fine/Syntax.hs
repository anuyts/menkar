{-# LANGUAGE UndecidableInstances #-}

module Menkar.PrettyPrint.Fine.Syntax where

import Menkar.Fine.Syntax
import Menkar.Basic.Context
import Menkar.PrettyPrint.Aux.Context
import qualified Menkar.Raw as Raw
import qualified Menkar.PrettyPrint.Raw as Raw
import Text.PrettyPrint.Tree
import Data.Void
import Data.Maybe
import Data.Proxy
import Control.Exception.AssertFalse
import Data.Functor.Compose
import Data.Functor.Const
import Control.Lens

class Fine2Pretty mode modty f where
  fine2pretty :: DeBruijnLevel v => ScCtx mode modty v Void -> f mode modty v -> PrettyTree String
  fine2string :: DeBruijnLevel v => ScCtx mode modty v Void -> f mode modty v -> String
  fine2string gamma x = render (RenderState 100 "  " "    ") $ fine2pretty gamma x

---------------------------

instance (Functor mode, Functor modty,
                  Fine2Pretty mode modty Mode, Fine2Pretty mode modty Modty) =>
         Fine2Pretty mode modty ModedModality where
  fine2pretty gamma (ModedModality d mu) = ribbonEmpty \\\ [
                "[" ++| fine2pretty gamma (Mode $ d) |++ "] ",
                "[" ++| fine2pretty gamma (Modty $ mu) |++ "] "
              ]
instance (Functor mode, Functor modty,
                  Fine2Pretty mode modty Mode, Fine2Pretty mode modty Modty) =>
         Show (ModedModality mode modty Void) where
  show dmu = "[ModedModality|\n" ++ fine2string ScCtxEmpty dmu ++ "\n]"

deriving instance (Show (mode v), Show (modty v)) => Show (ModedContramodality mode modty v)

binding2pretty :: (DeBruijnLevel v,
                  Functor mode, Functor modty,
                  Fine2Pretty mode modty Mode, Fine2Pretty mode modty Modty, Fine2Pretty mode modty rhs) =>
                  String -> ScCtx mode modty v Void -> Binding Type rhs mode modty v -> PrettyTree String
binding2pretty opstring gamma binding =
  fine2pretty gamma (binding'segment binding)
  \\\ [" " ++ opstring ++ " " ++|
       fine2pretty (gamma ::.. (VarFromCtx <$> segment2scSegment (binding'segment binding))) (binding'body binding)
      ]
instance (Functor mode, Functor modty,
         Fine2Pretty mode modty Mode, Fine2Pretty mode modty Modty, Fine2Pretty mode modty rhs) =>
         Fine2Pretty mode modty (Binding Type rhs) where
  fine2pretty gamma binding = binding2pretty ">" gamma binding
instance (Functor mode, Functor modty,
         Fine2Pretty mode modty Mode, Fine2Pretty mode modty Modty, Fine2Pretty mode modty rhs) =>
         Show (Binding Type rhs mode modty Void) where
  show binding = "[Binding|\n" ++ fine2string ScCtxEmpty binding ++ "\n]"

instance (Functor mode, Functor modty,
         Fine2Pretty mode modty Mode, Fine2Pretty mode modty Modty) =>
         Fine2Pretty mode modty UniHSConstructor where
  fine2pretty gamma (UniHS d lvl) =
    ribbon "UniHS " \\\ [
      fine2pretty gamma (Mode d),
      fine2pretty gamma lvl
      ]
  fine2pretty gamma (Pi binding) = binding2pretty "->" gamma binding
  fine2pretty gamma (Sigma binding) = binding2pretty "><" gamma binding
  fine2pretty gamma (EmptyType) = ribbon "Empty"
  fine2pretty gamma (UnitType) = ribbon "Unit"
  fine2pretty gamma (BoxType tySeg) = "Box " ++| fine2pretty gamma tySeg
  fine2pretty gamma (NatType) = ribbon "Nat"
instance (Functor mode, Functor modty,
         Fine2Pretty mode modty Mode, Fine2Pretty mode modty Modty) =>
         Show (UniHSConstructor mode modty Void) where
  show typeterm = "[UniHSConstructor|\n" ++ fine2string ScCtxEmpty typeterm ++ "\n]"
  
instance (Functor mode, Functor modty,
         Fine2Pretty mode modty Mode, Fine2Pretty mode modty Modty) =>
         Fine2Pretty mode modty ConstructorTerm where
  fine2pretty gamma (ConsUniHS typeterm) = fine2pretty gamma typeterm
    {-ribbon "withMode" \\\ [
      " " ++| fine2pretty gamma (Mode d),
      " (" ++| fine2pretty gamma typeterm |++ ")"
      ]-}
  fine2pretty gamma (Lam binding) = binding2pretty ">" gamma binding
  fine2pretty gamma (Pair binding tmFst tmSnd) =
    ribbon "ofType" \\\ [
      " (" ++| fine2pretty gamma (Sigma binding) |++ ")",
      " (" ++| fine2pretty gamma tmFst |++ " , " |+| fine2pretty gamma tmSnd |++ ")"
      ]
  fine2pretty gamma ConsUnit = ribbon "unit"
  fine2pretty gamma (ConsBox tySeg tmUnbox) =
    ribbon "ofType" \\\ [
      " (" ++| fine2pretty gamma (BoxType tySeg) |++ ")",
      " (box .{" ++| fine2pretty gamma tmUnbox |++ "} ...)"
      ]
  fine2pretty gamma (ConsZero) = ribbon "zero"
  fine2pretty gamma (ConsSuc t) = "suc .{" ++| fine2pretty gamma t |++ "}"
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
  fine2pretty gamma (SmartElimArg (Raw.ArgSpecNamed name) term) =
    ".{" ++ Raw.unparse name ++ " = " ++| fine2pretty gamma term |++ "}"
  fine2pretty gamma (SmartElimProj projSpec) = Raw.unparse' (Raw.ElimProj projSpec)
instance (Functor mode, Functor modty,
         Fine2Pretty mode modty Mode, Fine2Pretty mode modty Modty) =>
         Show (SmartEliminator mode modty Void) where
  show smartElim = "[SmartEliminator|\n" ++ fine2string ScCtxEmpty smartElim ++ "\n]"

elimination2pretty :: (DeBruijnLevel v,
                       Functor mode, Functor modty,
                       Fine2Pretty mode modty Mode, Fine2Pretty mode modty Modty) =>
         ScCtx mode modty v Void ->
         ModedModality mode modty v ->
         Term mode modty v ->
         UniHSConstructor mode modty v ->
         Eliminator mode modty v ->
         PrettyTree String
{-
--elimination2pretty gamma eliminee (ElimUnsafeResize) = "UnsafeResize (" ++| eliminee |++ ")"
elimination2pretty gamma eliminee (App piBinding arg) = 
    ribbon "(ofType" \\\ [
      " (" ++| fine2pretty gamma (Pi piBinding) |++ ")",
      " (" ++| eliminee |++ ")"
      ] ///
    ribbon ")" \\\
      [
      " .{" ++| fine2pretty gamma arg |++ "}"
      ]
elimination2pretty gamma eliminee (ElimSigma motive clause) =
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
elimination2pretty gamma eliminee (Unbox boxSeg) = todo
elimination2pretty gamma eliminee (ElimNat motive cz cs) = todo
-}
elimination2pretty gamma dmu eliminee tyEliminee (App arg) =
    ribbon "(ofType" \\\ [
      " (" ++| fine2pretty gamma tyEliminee |++ ")",
      " (" ++| fine2pretty gamma eliminee |++ ")"
      ] ///
    ribbon ")" \\\
      [
      " .{" ++| fine2pretty gamma arg |++ "}"
      ]
elimination2pretty gamma dmu eliminee tyEliminee (ElimDep motive (ElimSigma clausePair)) =
  ribbon "let {" \\\ [
    ribbon "elim f" \\\ [
        " : " ++| fine2pretty gamma (Pi (Binding
                                      (Declaration
                                        (DeclNameSegment $ _namedBinding'name motive)
                                        dmu
                                        Explicit
                                        (Type $ Expr3 $ TermCons $ ConsUniHS $ tyEliminee)
                                      )
                                      (unType $ _namedBinding'body motive)
                                    )),
        fine2pretty gamma $ ModuleRHS $ Compose $ [
                todo
            ]
        ]
    ] ///
  "} in f .{" ++| fine2pretty gamma eliminee |++ "}"
elimination2pretty gamma dmu eliminee tyEliminee eliminator = todo

{-
instance (Functor mode, Functor modty,
         Fine2Pretty mode modty Mode, Fine2Pretty mode modty Modty) =>
         Show (Eliminator mode modty Void) where
  show elim = "[Eliminator| x > " ++ render defaultRenderState (elimination2pretty ScCtxEmpty (ribbon "x") elim)
-}

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
  fine2pretty gamma (TermElim mod eliminee tyEliminee eliminator) =
    elimination2pretty gamma mod eliminee tyEliminee eliminator
  fine2pretty gamma (TermMeta i (Compose depcies)) = ribbon ("?" ++ show i) \\\ ((" " ++|) . fine2pretty gamma <$> depcies)
  fine2pretty gamma TermWildcard = ribbon "_"
  fine2pretty gamma (TermQName qname lookupresult) = Raw.unparse' qname
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

toSubscript :: String -> String
toSubscript = map (\ char -> toEnum $ fromEnum char - 48 + 8320)

instance (Functor mode, Functor modty,
         Fine2Pretty mode modty Mode, Fine2Pretty mode modty Modty, Fine2Pretty mode modty termNV) =>
         Fine2Pretty mode modty (Expr3 termNV) where
  fine2pretty gamma (Var3 v) = (fromMaybe (ribbon "_") $ Raw.unparse' <$> scGetName gamma v)
    |++ (toSubscript $ show $ getDeBruijnLevel Proxy v)
  fine2pretty gamma (Expr3 t) = fine2pretty gamma t
instance (Functor mode, Functor modty,
         Fine2Pretty mode modty Mode, Fine2Pretty mode modty Modty, Fine2Pretty mode modty termNV) =>
         Show (Expr3 termNV mode modty Void) where
  show e = "[Expr3|\n" ++ fine2string ScCtxEmpty e ++ "\n]"

----------------------

instance (Functor mode, Functor modty,
         Fine2Pretty mode modty Mode, Fine2Pretty mode modty Modty) =>
         Fine2Pretty mode modty Annotation where
  fine2pretty gamma (AnnotMode d) = fine2pretty gamma (Mode d)
  fine2pretty gamma (AnnotModality mu) = fine2pretty gamma (Modty mu)
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

declName2pretty :: forall v mode modty declSort . DeBruijnLevel v =>
  ScCtx mode modty v Void -> DeclName declSort -> PrettyTree String
declName2pretty gamma (DeclNameVal name) = Raw.unparse' name
declName2pretty gamma (DeclNameModule str) = ribbon str
declName2pretty gamma (DeclNameSegment maybeName) = (fromMaybe (ribbon "_") $ Raw.unparse' <$> maybeName)
                                              |++ (toSubscript $ show $ size (Proxy :: Proxy v))
declName2pretty gamma (DeclNameValSpec) = ribbon "<VALSPECNAME>"
instance Show (DeclName declSort) where
  show declName = "[DeclName|\n" ++ render defaultRenderState (declName2pretty ScCtxEmpty declName) ++ "\n]"

{-| Prettyprints a telescope. -}
telescope2pretties :: (DeBruijnLevel v,
         Functor mode, Functor modty, Functor (ty mode modty),
         Fine2Pretty mode modty Mode, Fine2Pretty mode modty Modty, Fine2Pretty mode modty ty) =>
         ScCtx mode modty v Void -> Telescope ty mode modty v -> [PrettyTree String]
telescope2pretties gamma (Telescoped Unit3) = []
telescope2pretties gamma (seg :|- telescope) =
  (fine2pretty gamma seg) : telescope2pretties (gamma ::.. (VarFromCtx <$> segment2scSegment seg)) telescope
telescope2pretties gamma (mu :** telescope) =
  [fine2pretty gamma (Modty $ modality'mod mu) |++ " {" \\\
    telescope2pretties (() ::\\ gamma) telescope /+/
    ribbon "}"
  ]
instance (Functor mode, Functor modty, Functor (ty mode modty),
         Fine2Pretty mode modty Mode, Fine2Pretty mode modty Modty, Fine2Pretty mode modty ty) =>
         Fine2Pretty mode modty (Telescope ty) where
  fine2pretty gamma telescope = treeGroup $ telescope2pretties gamma telescope
instance (Functor mode, Functor modty, Functor (ty mode modty),
         Fine2Pretty mode modty Mode, Fine2Pretty mode modty Modty, Fine2Pretty mode modty ty) =>
         Show (Telescope ty mode modty Void) where
  show theta = "[Telescope|\n" ++ fine2string ScCtxEmpty theta ++ "\n]"

declAnnots2pretties :: (DeBruijnLevel v,
         Functor mode, Functor modty,
         Fine2Pretty mode modty Mode, Fine2Pretty mode modty Modty) =>
         ScCtx mode modty v Void -> Declaration declSort content mode modty v -> [PrettyTree String]
declAnnots2pretties gamma decl = [
                fine2pretty gamma (_decl'plicity decl),
                "[" ++| fine2pretty gamma (Mode $ modality'dom $ _decl'modty decl) |++ "] ",
                "[" ++| fine2pretty gamma (Modty $ modality'mod $ _decl'modty decl) |++ "] "
              ]

{-
tdeclAnnots2pretties :: (Functor mode, Functor modty, Functor (ty mode modty),
         Fine2Pretty mode modty Mode, Fine2Pretty mode modty Modty, Fine2Pretty mode modty ty) =>
         ScCtx mode modty v Void -> TelescopedDeclaration declSort ty content mode modty v -> [PrettyTree String]
tdeclAnnots2pretties gamma tdecl =
        getConst (mapTelescopedSc (
            \ wkn gammadelta decl -> Const $ declAnnots2pretties gammadelta decl
          ) gamma tdecl)
-}

instance (Functor mode, Functor modty, Functor (ty mode modty),
         Fine2Pretty mode modty Mode, Fine2Pretty mode modty Modty, Fine2Pretty mode modty ty) =>
         Fine2Pretty mode modty (Segment ty) where
  fine2pretty gamma seg = ribbon " {" \\\
    prettyAnnots ///
    "| " ++| (declName2pretty gamma $ DeclNameSegment $ _segment'name seg) |++ " : " |+| prettyType |++ "}"
    where
      prettyAnnots = declAnnots2pretties gamma seg
      prettyType = fine2pretty gamma (_decl'content seg)
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
    \\\ declAnnots2pretties gamma val
    /// (declName2pretty gamma $ _decl'name val)
    \\\ telescope2pretties gamma (telescoped'telescope $ _decl'content val)
    /// prettyValRHS
    where
      prettyValRHS = 
        getConst (mapTelescopedScDB (
            \ wkn gammadelta t -> Const $ fine2pretty gammadelta t
          ) gamma $ _decl'content val)
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
    \\\ declAnnots2pretties gamma modul
    /// (declName2pretty gamma $ _decl'name modul)
    \\\ telescope2pretties gamma (telescoped'telescope $ _decl'content modul)
    /// prettyModuleRHS
    where
      prettyModuleRHS = 
        getConst (mapTelescopedScDB (
            \ wkn gammadelta modulRHS -> Const $ fine2pretty gammadelta modulRHS
          ) gamma $ _decl'content modul)
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
