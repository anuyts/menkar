{-# LANGUAGE UndecidableInstances #-}

module Menkar.PrettyPrint.Fine.Syntax where

import Menkar.Fine.Syntax
import Menkar.Basic.Context
import Menkar.Fine.Context
import Menkar.PrettyPrint.Aux.Context
import Menkar.Fine.LookupQName
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

charYielding :: Char
charYielding = '\x2198'

class Fine2Pretty sys f where
  fine2pretty :: DeBruijnLevel v => ScCtx sys v Void -> f sys v -> PrettyTree String
  fine2string :: DeBruijnLevel v => ScCtx sys v Void -> f sys v -> String
  fine2string gamma x = render (RenderState 100 "  " "    ") $ fine2pretty gamma x

---------------------------

instance (SysTrav sys,
                  Fine2Pretty sys Mode, Fine2Pretty sys Modality) =>
         Fine2Pretty sys ModedModality where
  fine2pretty gamma (ModedModality d mu) = ribbonEmpty \\\ [
                "d " ++| fine2pretty gamma d |++ " | ",
                "m " ++| fine2pretty gamma mu |++ " | "
              ]
instance (SysTrav sys,
                  Fine2Pretty sys Mode, Fine2Pretty sys Modality) =>
         Show (ModedModality sys Void) where
  show dmu = "[ModedModality|\n" ++ fine2string ScCtxEmpty dmu ++ "\n|]"

deriving instance (Show (Mode sys v), Show (Modality sys v)) => Show (ModedContramodality sys v)

binding2pretty :: (DeBruijnLevel v,
                  SysTrav sys,
                  Fine2Pretty sys Mode, Fine2Pretty sys Modality, Fine2Pretty sys rhs) =>
                  String -> ScCtx sys v Void -> Binding Type rhs sys v -> PrettyTree String
binding2pretty opstring gamma binding =
  fine2pretty gamma (binding'segment binding)
  \\\ [" " ++ opstring ++ " " ++|
       fine2pretty (gamma ::.. (VarFromCtx <$> segment2scSegment (binding'segment binding))) (binding'body binding)
      ]
instance (SysTrav sys,
         Fine2Pretty sys Mode, Fine2Pretty sys Modality, Fine2Pretty sys rhs) =>
         Fine2Pretty sys (Binding Type rhs) where
  fine2pretty gamma binding = binding2pretty ">" gamma binding
instance (SysTrav sys,
         Fine2Pretty sys Mode, Fine2Pretty sys Modality, Fine2Pretty sys rhs) =>
         Show (Binding Type rhs sys Void) where
  show binding = "[Binding|\n" ++ fine2string ScCtxEmpty binding ++ "\n|]"

instance (SysTrav sys,
         Fine2Pretty sys Mode, Fine2Pretty sys Modality) =>
         Fine2Pretty sys UniHSConstructor where
  fine2pretty gamma (UniHS d {-lvl-}) =
    ribbon "UniHS " \\\ [
      fine2pretty gamma d
      --, " (" ++| fine2pretty gamma lvl |++ ")"
      ]
  fine2pretty gamma (Pi binding) = binding2pretty "->" gamma binding
  fine2pretty gamma (Sigma binding) = binding2pretty "><" gamma binding
  fine2pretty gamma (EmptyType) = ribbon "Empty"
  fine2pretty gamma (UnitType) = ribbon "Unit"
  fine2pretty gamma (BoxType tySeg) = "Box" ++| fine2pretty gamma tySeg
  fine2pretty gamma (NatType) = ribbon "Nat"
  fine2pretty gamma (EqType tyAmbient tyL tyR) =
    ribbonEmpty
    \\\ ["(" ++| fine2pretty gamma tyL |++ ")"]
    /+/ " == .{" ++| fine2pretty gamma tyAmbient |++ "} "
    \\\ ["(" ++| fine2pretty gamma tyR |++ ")"]
instance (SysTrav sys,
         Fine2Pretty sys Mode, Fine2Pretty sys Modality) =>
         Show (UniHSConstructor sys Void) where
  show typeterm = "[UniHSConstructor|\n" ++ fine2string ScCtxEmpty typeterm ++ "\n|]"
  
instance (SysTrav sys,
         Fine2Pretty sys Mode, Fine2Pretty sys Modality) =>
         Fine2Pretty sys ConstructorTerm where
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
      " (box .{" ++| fine2pretty gamma tmUnbox |++ "})"
      ]
  fine2pretty gamma (ConsZero) = ribbon "zero"
  fine2pretty gamma (ConsSuc t) = "suc .{" ++| fine2pretty gamma t |++ "}"
  fine2pretty gamma ConsRefl = ribbon "refl"
instance (SysTrav sys,
         Fine2Pretty sys Mode, Fine2Pretty sys Modality) =>
         Show (ConstructorTerm sys Void) where
  show consTerm = "[ConstructorTerm|\n" ++ fine2string ScCtxEmpty consTerm ++ "\n|]"

instance (SysTrav sys,
         Fine2Pretty sys Mode, Fine2Pretty sys Modality) =>
         Fine2Pretty sys SmartEliminator where
  fine2pretty gamma (SmartElimDots) = ribbon "..."
  --fine2pretty gamma (SmartElimEnd argSpec) = Raw.unparse' (Raw.ElimEnd argSpec)
  fine2pretty gamma (SmartElimArg Raw.ArgSpecNext term) = ".{" ++| fine2pretty gamma term |++ "}"
  fine2pretty gamma (SmartElimArg Raw.ArgSpecExplicit term) = "(" ++| fine2pretty gamma term |++ ")"
  fine2pretty gamma (SmartElimArg (Raw.ArgSpecNamed name) term) =
    ".{" ++ Raw.unparse name ++ " = " ++| fine2pretty gamma term |++ "}"
  fine2pretty gamma (SmartElimProj projSpec) = Raw.unparse' (Raw.ElimProj projSpec)
instance (SysTrav sys,
         Fine2Pretty sys Mode, Fine2Pretty sys Modality) =>
         Show (SmartEliminator sys Void) where
  show smartElim = "[SmartEliminator|\n" ++ fine2string ScCtxEmpty smartElim ++ "\n|]"

typed2pretty :: (DeBruijnLevel v,
                       SysTrav sys,
                       Fine2Pretty sys Mode, Fine2Pretty sys Modality) =>
  ScCtx sys v Void ->
  Term sys v ->
  Type sys v ->
  PrettyTree String
typed2pretty gamma t ty = fine2pretty gamma t
{-  ribbon "(ofType" \\\ [
      " (" ++| fine2pretty gamma ty |++ ")",
      " (" ++| fine2pretty gamma t |++ ")"
    ] ///
  ribbon ")" -}

instance (SysTrav sys,
         Fine2Pretty sys Mode, Fine2Pretty sys Modality, Fine2Pretty sys rhs) =>
         Fine2Pretty sys (NamedBinding rhs) where
  fine2pretty gamma (NamedBinding maybeName body) =
    let gammaExt = gamma ::.. ScSegment maybeName
    in  var2pretty gammaExt VarLast |++ " > " |+| fine2pretty gammaExt body
instance (SysTrav sys,
         Fine2Pretty sys Mode, Fine2Pretty sys Modality, Fine2Pretty sys rhs) =>
         Show (NamedBinding rhs sys Void) where
  show binding = "[NamedBinding|\n" ++ fine2string ScCtxEmpty binding ++ "\n|]"

elimination2pretty :: (DeBruijnLevel v,
                       SysTrav sys,
                       Fine2Pretty sys Mode, Fine2Pretty sys Modality) =>
         ScCtx sys v Void ->
         ModedModality sys v ->
         Term sys v ->
         UniHSConstructor sys v ->
         Eliminator sys v ->
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
    "(" ++| typed2pretty gamma eliminee (Type $ Expr2 $ TermCons $ ConsUniHS $ tyEliminee) |++ ")" \\\
      [
      " .{" ++| fine2pretty gamma arg |++ "}"
      ]
elimination2pretty gamma dmu eliminee tyEliminee (Fst) =
  "(" ++| typed2pretty gamma eliminee (Type $ Expr2 $ TermCons $ ConsUniHS $ tyEliminee) |++ ") .1 "
elimination2pretty gamma dmu eliminee tyEliminee (Snd) =
  "(" ++| typed2pretty gamma eliminee (Type $ Expr2 $ TermCons $ ConsUniHS $ tyEliminee) |++ ") ..2 "
elimination2pretty gamma dmu eliminee tyEliminee (Unbox) =
  "unbox (" ++| typed2pretty gamma eliminee (Type $ Expr2 $ TermCons $ ConsUniHS $ tyEliminee) |++ ") "
elimination2pretty gamma dmu eliminee tyEliminee (Funext) =
  "funext (" ++| typed2pretty gamma eliminee (Type $ Expr2 $ TermCons $ ConsUniHS $ tyEliminee) |++ ") "
elimination2pretty gamma dmu eliminee tyEliminee (ElimDep motive (ElimSigma clausePair)) =
  ribbon "indSigma " \\\ [
      fine2pretty gamma dmu,
      "(" ++| fine2pretty gamma motive |++ ") ",
      "(" ++| fine2pretty gamma clausePair |++ ") ",
      "(" ++| typed2pretty gamma eliminee (Type $ Expr2 $ TermCons $ ConsUniHS $ tyEliminee) |++ ") "
    ]
  {-
  ribbon "let {" \\\ [
    ribbon "elim f" \\\ [
        " : " ++| fine2pretty gamma (Pi (Binding
                                      (Declaration
                                        (DeclNameSegment $ _namedBinding'name motive)
                                        dmu
                                        Explicit
                                        (Type $ Expr2 $ TermCons $ ConsUniHS $ tyEliminee)
                                      )
                                      (unType $ _namedBinding'body motive)
                                    )),
        fine2pretty gamma $ ModuleRHS $ Compose $ [
                todo
            ]
        ]
    ] ///
  "} in f .{" ++| fine2pretty gamma eliminee |++ "}"
  -}
elimination2pretty gamma dmu eliminee tyEliminee (ElimDep motive (ElimBox clauseBox)) =
  ribbon "indBox " \\\ [
      fine2pretty gamma dmu,
      "(" ++| fine2pretty gamma motive |++ ") ",
      "(" ++| fine2pretty gamma clauseBox |++ ") ",
      "(" ++| typed2pretty gamma eliminee (Type $ Expr2 $ TermCons $ ConsUniHS $ tyEliminee) |++ ") "
    ]
elimination2pretty gamma dmu eliminee tyEliminee (ElimDep motive (ElimEmpty)) =
  ribbon "indEmpty " \\\ [
      fine2pretty gamma dmu,
      "(" ++| fine2pretty gamma motive |++ ") ",
      "(" ++| typed2pretty gamma eliminee (Type $ Expr2 $ TermCons $ ConsUniHS $ tyEliminee) |++ ") "
    ]
elimination2pretty gamma dmu eliminee tyEliminee (ElimDep motive (ElimNat clauseZero clauseSuc)) =
  ribbon "indNat " \\\ [
      fine2pretty gamma dmu,
      "(" ++| fine2pretty gamma motive |++ ") ",
      "(" ++| fine2pretty gamma clauseZero |++ ") ",
      "(" ++| fine2pretty gamma clauseSuc |++ ") ",
      "(" ++| typed2pretty gamma eliminee (Type $ Expr2 $ TermCons $ ConsUniHS $ tyEliminee) |++ ") "
    ]
elimination2pretty gamma dmu eliminee tyEliminee (ElimEq motive crefl) =
  ribbon "ind== " \\\ [
      fine2pretty gamma dmu,
      "(" ++| fine2pretty gamma motive |++ ") ",
      "(" ++| fine2pretty gamma crefl |++ ") ",
      "(" ++| typed2pretty gamma eliminee (hs2type tyEliminee) |++ ") "
    ]
--elimination2pretty gamma dmu eliminee tyEliminee eliminator = todo

{-
instance (SysTrav sys,
         Fine2Pretty sys Mode, Fine2Pretty sys Modality) =>
         Show (Eliminator sys Void) where
  show elim = "[Eliminator| x > " ++ render defaultRenderState (elimination2pretty ScCtxEmpty (ribbon "x") elim)
-}

instance (SysTrav sys,
         Fine2Pretty sys Mode, Fine2Pretty sys Modality) =>
         Fine2Pretty sys Type where
  fine2pretty gamma (Type t) = fine2pretty gamma t
deriving instance (SysTrav sys,
                   Fine2Pretty sys Mode, Fine2Pretty sys Modality)
    => Show (Type sys Void)

var2pretty :: DeBruijnLevel v => ScCtx sys v Void -> v -> PrettyTree String
var2pretty gamma v = (fromMaybe (ribbon "_") $ Raw.unparse' <$> scGetName gamma v)
    |++ (toSubscript $ show $ getDeBruijnLevel Proxy v)

instance (SysTrav sys,
         Fine2Pretty sys Mode, Fine2Pretty sys Modality) =>
         Fine2Pretty sys TermNV where
  fine2pretty gamma (TermCons consTerm) = fine2pretty gamma consTerm
  fine2pretty gamma (TermElim mod eliminee tyEliminee eliminator) =
    elimination2pretty gamma mod eliminee tyEliminee eliminator
  fine2pretty gamma (TermMeta etaFlag i (Compose depcies)) =
    ribbon ("?" ++ show i ++ (if etaFlag then "" else "-no-eta"))
    \\\ ((|++ "}") . (" .{" ++|) . fine2pretty gamma <$> depcies)
  fine2pretty gamma TermWildcard = ribbon "_"
  fine2pretty gamma (TermQName qname lookupresult) = Raw.unparse' qname
    {-
    case _leftDivided'content lookupresult of
      (dmu :** telescopedVal) -> getConst $ mapTelescopedSc
        (\ wkn gammadelta valRHS -> case _val'term valRHS of
            Var2 v -> haveScDB gammadelta $ Const $ var2pretty gammadelta v
            _ -> Const $ Raw.unparse' qname
        ) gamma telescopedVal
      _ -> Raw.unparse' qname
    -}
    --case _leftDivided'content lookupresult of
    --Telescoped (ValRHS (Var2 v) _) -> var2pretty gamma v
    --_ -> Raw.unparse' qname
  fine2pretty gamma (TermSmartElim eliminee (Compose eliminators) result) =
    "(" ++| fine2pretty gamma eliminee |++ ")"
      |+| treeGroup ((" " ++|) . fine2pretty gamma <$> eliminators)
      |++ " \x2198 " |+| fine2pretty gamma result
  fine2pretty gamma (TermGoal str result) =
    "?" ++ str ++ " \x2198 " ++| fine2pretty gamma result
  fine2pretty gamma (TermProblem t) = "(! " ++| fine2pretty gamma t |++ "!)"
instance (SysTrav sys,
         Fine2Pretty sys Mode, Fine2Pretty sys Modality) =>
         Show (TermNV sys Void) where
  show t = "[TermNV|\n" ++ fine2string ScCtxEmpty t ++ "\n|]"

toSubscript :: String -> String
toSubscript = map (\ char -> toEnum $ fromEnum char - 48 + 8320)

instance (SysTrav sys,
         Fine2Pretty sys Mode, Fine2Pretty sys Modality, Fine2Pretty sys termNV) =>
         Fine2Pretty sys (Expr2 termNV) where
  fine2pretty gamma (Var2 v) = var2pretty gamma v
  fine2pretty gamma (Expr2 t) = fine2pretty gamma t
instance (SysTrav sys,
         Fine2Pretty sys Mode, Fine2Pretty sys Modality, Fine2Pretty sys termNV) =>
         Show (Expr2 termNV sys Void) where
  show e = "[Expr2|\n" ++ fine2string ScCtxEmpty e ++ "\n|]"

----------------------

instance (SysTrav sys,
         Fine2Pretty sys Mode, Fine2Pretty sys Modality) =>
         Fine2Pretty sys Annotation where
  fine2pretty gamma (AnnotMode d) = fine2pretty gamma d
  fine2pretty gamma (AnnotModality mu) = fine2pretty gamma mu
  fine2pretty gamma (AnnotImplicit) = ribbon "~"
instance (SysTrav sys,
         Fine2Pretty sys Mode, Fine2Pretty sys Modality) =>
         Show (Annotation sys Void) where
  show annot = "[Annotation|\n" ++ fine2string ScCtxEmpty annot ++ "\n|]"

instance (SysTrav sys,
         Fine2Pretty sys Mode, Fine2Pretty sys Modality) =>
         Fine2Pretty sys Plicity where
  fine2pretty gamma Explicit = ribbonEmpty
  fine2pretty gamma Implicit = ribbon "~ | "
  fine2pretty gamma (Resolves t) = "resolves " ++| fine2pretty gamma t |++ " | "
instance (SysTrav sys,
         Fine2Pretty sys Mode, Fine2Pretty sys Modality) =>
         Show (Plicity sys Void) where
  show plic = "[Plicity|\n" ++ fine2string ScCtxEmpty plic ++ "\n|]"

declName2pretty :: forall v sys declSort . DeBruijnLevel v =>
  ScCtx sys v Void -> DeclName declSort -> PrettyTree String
declName2pretty gamma (DeclNameVal name) = Raw.unparse' name
declName2pretty gamma (DeclNameModule str) = ribbon str
declName2pretty gamma (DeclNameSegment maybeName) = (fromMaybe (ribbon "_") $ Raw.unparse' <$> maybeName)
                                              |++ (toSubscript $ show $ size (Proxy :: Proxy v))
declName2pretty gamma (DeclNameValSpec) = ribbon "<VALSPECNAME>"
instance Show (DeclName declSort) where
  show declName = "[DeclName|\n" ++ render defaultRenderState (declName2pretty ScCtxEmpty declName) ++ "\n|]"

{-| Prettyprints a telescope. -}
telescope2pretties :: (DeBruijnLevel v,
         SysTrav sys, Functor (ty sys),
         Fine2Pretty sys Mode, Fine2Pretty sys Modality, Fine2Pretty sys ty) =>
         ScCtx sys v Void -> Telescope ty sys v -> [PrettyTree String]
telescope2pretties gamma (Telescoped Unit2) = []
telescope2pretties gamma (seg :|- telescope) =
  (fine2pretty gamma seg) : telescope2pretties (gamma ::.. (VarFromCtx <$> segment2scSegment seg)) telescope
telescope2pretties gamma (mu :** telescope) =
  [fine2pretty gamma (modality'mod mu) |++ " {" \\\
    telescope2pretties (() ::\\ gamma) telescope /+/
    ribbon "}"
  ]
instance (SysTrav sys, Functor (ty sys),
         Fine2Pretty sys Mode, Fine2Pretty sys Modality, Fine2Pretty sys ty) =>
         Fine2Pretty sys (Telescope ty) where
  fine2pretty gamma telescope = treeGroup $ telescope2pretties gamma telescope
instance (SysTrav sys, Functor (ty sys),
         Fine2Pretty sys Mode, Fine2Pretty sys Modality, Fine2Pretty sys ty) =>
         Show (Telescope ty sys Void) where
  show theta = "[Telescope|\n" ++ fine2string ScCtxEmpty theta ++ "\n|]"

declAnnots2pretties :: (DeBruijnLevel v,
         SysTrav sys,
         Fine2Pretty sys Mode, Fine2Pretty sys Modality) =>
         ScCtx sys v Void -> Declaration declSort content sys v -> [PrettyTree String]
declAnnots2pretties gamma decl = [
                fine2pretty gamma (_decl'modty decl),
                fine2pretty gamma (_decl'plicity decl)
              ]

{-
tdeclAnnots2pretties :: (SysTrav sys, Functor (ty sys),
         Fine2Pretty sys Mode, Fine2Pretty sys Modality, Fine2Pretty sys ty) =>
         ScCtx sys v Void -> TelescopedDeclaration declSort ty content sys v -> [PrettyTree String]
tdeclAnnots2pretties gamma tdecl =
        getConst (mapTelescopedSc (
            \ wkn gammadelta decl -> Const $ declAnnots2pretties gammadelta decl
          ) gamma tdecl)
-}

instance (SysTrav sys, Functor (ty sys),
         Fine2Pretty sys Mode, Fine2Pretty sys Modality, Fine2Pretty sys ty) =>
         Fine2Pretty sys (Segment ty) where
  fine2pretty gamma seg = ribbon " {" \\\
    prettyAnnots ///
    (declName2pretty gamma $ DeclNameSegment $ _segment'name seg) |++ " : " |+| prettyType |++ "}"
    where
      prettyAnnots = declAnnots2pretties gamma seg
      prettyType = fine2pretty gamma (_decl'content seg)
instance (SysTrav sys, Functor (ty sys),
         Fine2Pretty sys Mode, Fine2Pretty sys Modality, Fine2Pretty sys ty) =>
         Show (Segment ty sys Void) where
  show seg = "[Segment|\n" ++ fine2string ScCtxEmpty seg ++ "\n|]"

instance (SysTrav sys,
         Fine2Pretty sys Mode, Fine2Pretty sys Modality) =>
         Fine2Pretty sys ValRHS where
  fine2pretty gamma (ValRHS tm ty) = treeGroup [
      " : " ++| fine2pretty gamma ty,
      " = " ++| fine2pretty gamma tm
    ]
instance (SysTrav sys,
         Fine2Pretty sys Mode, Fine2Pretty sys Modality) =>
         Show (ValRHS sys Void) where
  show valRHS = "[ValRHS|\n" ++ fine2string ScCtxEmpty valRHS ++ "\n|]"

instance (SysTrav sys,
         Fine2Pretty sys Mode, Fine2Pretty sys Modality) =>
         Fine2Pretty sys Val where
  fine2pretty gamma val =
    ribbon "val ["
    \\\ declAnnots2pretties gamma val
    /// "] " ++| (declName2pretty gamma $ _decl'name val)
    \\\ telescope2pretties gamma (telescoped'telescope $ _decl'content val)
    /// prettyValRHS
    where
      prettyValRHS = 
        getConst (mapTelescopedScDB (
            \ wkn gammadelta t -> Const $ fine2pretty gammadelta t
          ) gamma $ _decl'content val)
instance (SysTrav sys,
         Fine2Pretty sys Mode, Fine2Pretty sys Modality) =>
         Show (Val sys Void) where
  show val = "[Val|\n" ++ fine2string ScCtxEmpty val ++ "\n|]"
        
instance (SysTrav sys,
         Fine2Pretty sys Mode, Fine2Pretty sys Modality) =>
         Fine2Pretty sys ModuleRHS where
  fine2pretty gamma moduleRHS = ribbon " where {"
    \\\ ((fine2pretty (gamma ::<...> (VarFromCtx <$> moduleRHS)) <$> (reverse $ view moduleRHS'entries moduleRHS))
          >>= (\ entry -> [entry, ribbon "        "]))
    /// ribbon "}"
instance (SysTrav sys,
         Fine2Pretty sys Mode, Fine2Pretty sys Modality) =>
         Show (ModuleRHS sys Void) where
  show moduleRHS = "[ModuleRHS|\n" ++ fine2string ScCtxEmpty moduleRHS ++ "\n|]"

instance (SysTrav sys,
         Fine2Pretty sys Mode, Fine2Pretty sys Modality) =>
         Fine2Pretty sys Module where
  fine2pretty gamma modul =
    ribbon "module  ["
    \\\ declAnnots2pretties gamma modul
    /// "] " ++| (declName2pretty gamma $ _decl'name modul)
    \\\ telescope2pretties gamma (telescoped'telescope $ _decl'content modul)
    /// prettyModuleRHS
    where
      prettyModuleRHS = 
        getConst (mapTelescopedScDB (
            \ wkn gammadelta modulRHS -> Const $ fine2pretty gammadelta modulRHS
          ) gamma $ _decl'content modul)
instance (SysTrav sys,
         Fine2Pretty sys Mode, Fine2Pretty sys Modality) =>
         Show (Module sys Void) where
  show modul = "[Module|\n" ++ fine2string ScCtxEmpty modul ++ "\n|]"

instance (SysTrav sys,
         Fine2Pretty sys Mode, Fine2Pretty sys Modality) =>
         Fine2Pretty sys Entry where
  fine2pretty gamma (EntryVal val) = fine2pretty gamma val
  fine2pretty gamma (EntryModule modul) = fine2pretty gamma modul
instance (SysTrav sys,
         Fine2Pretty sys Mode, Fine2Pretty sys Modality) =>
         Show (Entry sys Void) where
  show entry = "[Entry|\n" ++ fine2string ScCtxEmpty entry ++ "\n|]"

instance (SysTrav sys, Functor (ty sys),
         Fine2Pretty sys Mode, Fine2Pretty sys Modality, Fine2Pretty sys ty) =>
         Fine2Pretty sys (Twice2 ty) where
  fine2pretty gamma (Twice2 ty1 ty2) =
    ribbonEmpty \\\ [fine2pretty gamma ty1, ribbon " =[]= ", fine2pretty gamma ty2]
