{-# LANGUAGE UndecidableInstances #-}

module Menkar.PrettyPrint.Fine.Syntax where

import Prelude hiding (lookup)

import Menkar.Fine.Syntax
import Menkar.Basic.Context
import Menkar.Fine.Context
import Menkar.PrettyPrint.Aux.Context
import Menkar.Fine.LookupQName
import Menkar.Fine.Multimode
import qualified Menkar.Raw as Raw
import qualified Menkar.PrettyPrint.Raw as Raw

import Text.PrettyPrint.Tree
import Data.Omissible

import Data.Void
import Data.Maybe
import Data.Proxy
import Control.Exception.AssertFalse
import Data.Functor.Compose
import Data.Functor.Const
import Control.Lens
import Control.Monad
import Data.Number.Nat
import Data.IntMap.Lazy hiding (map, size)

charYielding :: Char
charYielding = '\x2198'

data PrintEntryVerbosity = PrintEntryName | PrintEntryNameAnnots | PrintEntryEntirely

{-| @'PrintModuleVerbosity' Nothing@ indicates that module contents should not be printed.
    @'PrintModuleVerbosity' (Just p)@ indicates that module contents should be printed according to @p@.
-}
data PrintModuleVerbosity = PrintModuleVerbosity {unPrintModuleVerbosity :: Maybe PrintEntryVerbosity}
  --PrintModuleDots | PrintModuleNames | {-PrintModuleTypes |-} PrintModuleContents

data PrintAlgorithmVerbosity = PrintAlgorithm | PrintAlgorithmUnderscore | DontPrintAlgorithm

data Fine2PrettyOptions sys = Fine2PrettyOptions {
  -- | How to render.
  _fine2pretty'renderOptions :: RenderOptions,
  -- | Instead of listing all dependencies, plug them into the smart elimination / ... being resolved.
  _fine2pretty'humanReadableMetas :: Bool,
  _fine2pretty'printAlgorithm :: PrintAlgorithmVerbosity,
  -- | When printing a solved meta, print its solution instead.
  _fine2pretty'printSolutions :: Maybe (IntMap (ForSomeDeBruijnLevel (Term sys))),
  -- | When printing contexts, explicity print left divisions, rather than computing the divided
  -- | modality.
  _fine2pretty'explicitLeftDivision :: Bool,
  _fine2pretty'printTypeAnnotations :: Bool,
  _fine2pretty'printModule :: PrintModuleVerbosity,
  _fine2pretty'printModuleInContext :: Maybe (PrintModuleVerbosity),
  _fine2pretty'printEntry :: PrintEntryVerbosity
  }

makeLenses ''Fine2PrettyOptions

instance Omissible (Fine2PrettyOptions sys) where
  omit = Fine2PrettyOptions {
    _fine2pretty'renderOptions = omit,
    _fine2pretty'humanReadableMetas = True,
    _fine2pretty'printAlgorithm = PrintAlgorithmUnderscore,
    _fine2pretty'printSolutions = Nothing,
    _fine2pretty'explicitLeftDivision = False,
    _fine2pretty'printTypeAnnotations = False,
    _fine2pretty'printModule = (PrintModuleVerbosity (Just PrintEntryEntirely)),
    _fine2pretty'printModuleInContext = (Just (PrintModuleVerbosity Nothing)),
    _fine2pretty'printEntry = PrintEntryEntirely}

---------------------------

class Fine2Pretty sys t | t -> sys where
  fine2pretty :: forall v . DeBruijnLevel v => ScCtx sys v Void -> t v -> Fine2PrettyOptions sys -> PrettyTree String
  fine2string :: forall v . DeBruijnLevel v => ScCtx sys v Void -> t v -> Fine2PrettyOptions sys -> String
  fine2string gamma x opts = render (fine2pretty gamma x opts) $ _fine2pretty'renderOptions opts

---------------------------

instance (SysSyntax (Term sys) sys,
          Fine2Pretty sys (Mode sys), Fine2Pretty sys (Modality sys)) =>
         Fine2Pretty sys (ModedModality sys) where
  fine2pretty gamma (ModedModality d mu) opts = ribbonEmpty \\\ [
                "d " ++| fine2pretty gamma d opts |++ " | ",
                "m " ++| fine2pretty gamma mu opts |++ " | "
              ]
instance (SysSyntax (Term sys) sys,
          Fine2Pretty sys (Mode sys), Fine2Pretty sys (Modality sys)) =>
         Show (ModedModality sys Void) where
  show dmu = "[ModedModality|\n" ++ fine2string ScCtxEmpty dmu omit ++ "\n|]"

deriving instance (Show (Mode sys v), Show (Modality sys v)) => Show (ModedContramodality sys v)

binding2pretty :: (DeBruijnLevel v,
                  SysSyntax (Term sys) sys,
                  Fine2Pretty sys (Mode sys), Fine2Pretty sys (Modality sys), Fine2Pretty sys (rhs sys)) =>
                  String -> ScCtx sys v Void -> Binding Type rhs sys v -> Fine2PrettyOptions sys -> PrettyTree String
binding2pretty opstring gamma binding opts =
  fine2pretty gamma (binding'segment binding) opts
  \\\ [" " ++ opstring ++ " " ++|
       fine2pretty (gamma ::.. (VarFromCtx <$> segment2scSegment (binding'segment binding))) (binding'body binding) opts
      ]
instance (SysSyntax (Term sys) sys,
         Fine2Pretty sys (Mode sys), Fine2Pretty sys (Modality sys), Fine2Pretty sys (rhs sys)) =>
         Fine2Pretty sys (Binding Type rhs sys) where
  fine2pretty gamma binding opts = binding2pretty ">" gamma binding opts
instance (SysSyntax (Term sys) sys,
         Fine2Pretty sys (Mode sys), Fine2Pretty sys (Modality sys), Fine2Pretty sys (rhs sys)) =>
         Show (Binding Type rhs sys Void) where
  show binding = "[Binding|\n" ++ fine2string ScCtxEmpty binding omit ++ "\n|]"

instance (SysSyntax (Term sys) sys,
         Fine2Pretty sys (Mode sys), Fine2Pretty sys (Modality sys)) =>
         Fine2Pretty sys (UniHSConstructor sys) where
  fine2pretty gamma (UniHS d {-lvl-}) opts =
    ribbon "UniHS " \\\ [
      fine2pretty gamma d opts
      --, " (" ++| fine2pretty gamma lvl |++ ")"
      ]
  fine2pretty gamma (Pi binding) opts = binding2pretty "->" gamma binding opts
  fine2pretty gamma (Sigma binding) opts = binding2pretty "><" gamma binding opts
  fine2pretty gamma (EmptyType) opts = ribbon "Empty"
  fine2pretty gamma (UnitType) opts = ribbon "Unit"
  fine2pretty gamma (BoxType tySeg) opts = "Box" ++| fine2pretty gamma tySeg opts
  fine2pretty gamma (NatType) opts = ribbon "Nat"
  fine2pretty gamma (EqType tyAmbient tyL tyR) opts =
    ribbonEmpty
    \\\ ["(" ++| fine2pretty gamma tyL opts |++ ")"]
    /+/ " == .{" ++| fine2pretty gamma tyAmbient opts |++ "} "
    \\\ ["(" ++| fine2pretty gamma tyR opts |++ ")"]
instance (SysSyntax (Term sys) sys,
         Fine2Pretty sys (Mode sys), Fine2Pretty sys (Modality sys)) =>
         Show (UniHSConstructor sys Void) where
  show typeterm = "[UniHSConstructor|\n" ++ fine2string ScCtxEmpty typeterm omit ++ "\n|]"
  
instance (SysSyntax (Term sys) sys,
         Fine2Pretty sys (Mode sys), Fine2Pretty sys (Modality sys)) =>
         Fine2Pretty sys (ConstructorTerm sys) where
  fine2pretty gamma (ConsUniHS typeterm) opts = fine2pretty gamma typeterm opts
    {-ribbon "withMode" \\\ [
      " " ++| fine2pretty gamma (Mode d),
      " (" ++| fine2pretty gamma typeterm |++ ")"
      ]-}
  fine2pretty gamma (Lam binding) opts = binding2pretty ">" gamma binding opts
  fine2pretty gamma (Pair binding tmFst tmSnd) opts =
    ribbon "ofType" \\\ [
      " (" ++| fine2pretty gamma (Sigma binding) opts |++ ")",
      " (" ++| fine2pretty gamma tmFst opts |++ " , " |+| fine2pretty gamma tmSnd opts |++ ")"
      ]
  fine2pretty gamma ConsUnit opts = ribbon "unit"
  fine2pretty gamma (ConsBox tySeg tmUnbox) opts =
    ribbon "ofType" \\\ [
      " (" ++| fine2pretty gamma (BoxType tySeg) opts |++ ")",
      " (box .{" ++| fine2pretty gamma tmUnbox opts |++ "})"
      ]
  fine2pretty gamma (ConsZero) opts = ribbon "zero"
  fine2pretty gamma (ConsSuc t) opts = "suc .{" ++| fine2pretty gamma t opts |++ "}"
  fine2pretty gamma ConsRefl opts = ribbon "refl"
instance (SysSyntax (Term sys) sys,
         Fine2Pretty sys (Mode sys), Fine2Pretty sys (Modality sys)) =>
         Show (ConstructorTerm sys Void) where
  show consTerm = "[ConstructorTerm|\n" ++ fine2string ScCtxEmpty consTerm omit ++ "\n|]"

instance (SysSyntax (Term sys) sys,
         Fine2Pretty sys (Mode sys), Fine2Pretty sys (Modality sys)) =>
         Fine2Pretty sys (SmartEliminator sys) where
  fine2pretty gamma (SmartElimDots) opts = ribbon "..."
  --fine2pretty gamma (SmartElimEnd argSpec) = Raw.unparse' (Raw.ElimEnd argSpec)
  fine2pretty gamma (SmartElimArg Raw.ArgSpecNext term) opts = ".{" ++| fine2pretty gamma term opts |++ "}"
  fine2pretty gamma (SmartElimArg Raw.ArgSpecExplicit term) opts = "(" ++| fine2pretty gamma term opts |++ ")"
  fine2pretty gamma (SmartElimArg (Raw.ArgSpecNamed name) term) opts =
    ".{" ++ Raw.unparse name ++ " = " ++| fine2pretty gamma term opts |++ "}"
  fine2pretty gamma (SmartElimProj projSpec) opts = Raw.unparse' (Raw.ElimProj projSpec)
instance (SysSyntax (Term sys) sys,
         Fine2Pretty sys (Mode sys), Fine2Pretty sys (Modality sys)) =>
         Show (SmartEliminator sys Void) where
  show smartElim = "[SmartEliminator|\n" ++ fine2string ScCtxEmpty smartElim omit ++ "\n|]"

typed2pretty :: (DeBruijnLevel v,
                       SysSyntax (Term sys) sys,
                       Fine2Pretty sys (Mode sys), Fine2Pretty sys (Modality sys)) =>
  ScCtx sys v Void ->
  Term sys v ->
  Type sys v ->
  Fine2PrettyOptions sys ->
  PrettyTree String
typed2pretty gamma t ty opts
  | _fine2pretty'printTypeAnnotations opts =
      ribbon "(ofType" \\\ [
          " (" ++| fine2pretty gamma ty opts |++ ")",
          " (" ++| fine2pretty gamma t opts |++ ")"
        ] ///
      ribbon ")"
  | otherwise = fine2pretty gamma t opts

instance (SysSyntax (Term sys) sys,
         Fine2Pretty sys (Mode sys), Fine2Pretty sys (Modality sys), Fine2Pretty sys (rhs sys)) =>
         Fine2Pretty sys (NamedBinding rhs sys) where
  fine2pretty gamma (NamedBinding maybeName body) opts =
    let gammaExt = gamma ::.. ScSegment maybeName
    in  var2pretty gammaExt VarLast opts |++ " > " |+| fine2pretty gammaExt body opts
instance (SysSyntax (Term sys) sys,
         Fine2Pretty sys (Mode sys), Fine2Pretty sys (Modality sys), Fine2Pretty sys (rhs sys)) =>
         Show (NamedBinding rhs sys Void) where
  show binding = "[NamedBinding|\n" ++ fine2string ScCtxEmpty binding omit ++ "\n|]"

elimination2pretty :: (DeBruijnLevel v,
                       SysSyntax (Term sys) sys,
                       Fine2Pretty sys (Mode sys), Fine2Pretty sys (Modality sys)) =>
         ScCtx sys v Void ->
         ModedModality sys v ->
         Term sys v ->
         UniHSConstructor sys v ->
         Eliminator sys v ->
         Fine2PrettyOptions sys ->
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
elimination2pretty gamma dmu eliminee tyEliminee (App arg) opts =
    "(" ++| typed2pretty gamma eliminee (hs2type $ tyEliminee) opts |++ ")" \\\
      [
      " .{" ++| fine2pretty gamma arg opts |++ "}"
      ]
elimination2pretty gamma dmu eliminee tyEliminee (Fst) opts =
  "(" ++| typed2pretty gamma eliminee (hs2type $ tyEliminee) opts |++ ") .1 "
elimination2pretty gamma dmu eliminee tyEliminee (Snd) opts =
  "(" ++| typed2pretty gamma eliminee (hs2type $ tyEliminee) opts |++ ") ..2 "
elimination2pretty gamma dmu eliminee tyEliminee (Unbox) opts =
  "unbox (" ++| typed2pretty gamma eliminee (hs2type $ tyEliminee) opts |++ ") "
elimination2pretty gamma dmu eliminee tyEliminee (Funext) opts =
  "funext (" ++| typed2pretty gamma eliminee (hs2type $ tyEliminee) opts |++ ") "
elimination2pretty gamma dmu eliminee tyEliminee (ElimDep motive (ElimSigma clausePair)) opts =
  ribbon "indSigma " \\\ [
      fine2pretty gamma dmu opts,
      "(" ++| fine2pretty gamma motive opts |++ ") ",
      "(" ++| fine2pretty gamma clausePair opts |++ ") ",
      "(" ++| typed2pretty gamma eliminee (hs2type $ tyEliminee) opts |++ ") "
    ]
  {-
  ribbon "let {" \\\ [
    ribbon "elim f" \\\ [
        " : " ++| fine2pretty gamma (Pi (Binding
                                      (Declaration
                                        (DeclNameSegment $ _namedBinding'name motive)
                                        dmu
                                        Explicit
                                        (hs2type $ tyEliminee)
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
elimination2pretty gamma dmu eliminee tyEliminee (ElimDep motive (ElimBox clauseBox)) opts =
  ribbon "indBox " \\\ [
      fine2pretty gamma dmu opts,
      "(" ++| fine2pretty gamma motive opts |++ ") ",
      "(" ++| fine2pretty gamma clauseBox opts |++ ") ",
      "(" ++| typed2pretty gamma eliminee (hs2type $ tyEliminee) opts |++ ") "
    ]
elimination2pretty gamma dmu eliminee tyEliminee (ElimDep motive (ElimEmpty)) opts =
  ribbon "indEmpty " \\\ [
      fine2pretty gamma dmu opts,
      "(" ++| fine2pretty gamma motive opts |++ ") ",
      "(" ++| typed2pretty gamma eliminee (hs2type $ tyEliminee) opts |++ ") "
    ]
elimination2pretty gamma dmu eliminee tyEliminee (ElimDep motive (ElimNat clauseZero clauseSuc)) opts =
  ribbon "indNat " \\\ [
      fine2pretty gamma dmu opts,
      "(" ++| fine2pretty gamma motive opts |++ ") ",
      "(" ++| fine2pretty gamma clauseZero opts |++ ") ",
      "(" ++| fine2pretty gamma clauseSuc opts |++ ") ",
      "(" ++| typed2pretty gamma eliminee (hs2type $ tyEliminee) opts |++ ") "
    ]
elimination2pretty gamma dmu eliminee tyEliminee (ElimEq motive crefl) opts =
  ribbon "ind== " \\\ [
      fine2pretty gamma dmu opts,
      "(" ++| fine2pretty gamma motive opts |++ ") ",
      "(" ++| fine2pretty gamma crefl opts |++ ") ",
      "(" ++| typed2pretty gamma eliminee (hs2type tyEliminee) opts |++ ") "
    ]
--elimination2pretty gamma dmu eliminee tyEliminee eliminator = todo

{-
instance (SysSyntax (Term sys) sys,
         Fine2Pretty sys (Mode sys), Fine2Pretty sys (Modality sys)) =>
         Show (Eliminator sys Void) where
  show elim = "[Eliminator| x > " ++ render defaultRenderState (elimination2pretty ScCtxEmpty (ribbon "x") elim)
-}

instance (SysSyntax (Term sys) sys,
         Fine2Pretty sys (Mode sys), Fine2Pretty sys (Modality sys)) =>
         Fine2Pretty sys (Algorithm sys) where
  fine2pretty gamma (AlgGoal str (Compose depcies)) opts =
    ribbon ("?" ++ str)
      \\\ ((|++ "}") . (" .{" ++|) . ($ opts) . fine2pretty gamma <$> depcies)
  fine2pretty gamma (AlgSmartElim eliminee (Compose eliminators)) opts =
    "(" ++| fine2pretty gamma eliminee opts |++ ")"
      |+| treeGroup ((" " ++|) . ($ opts) . fine2pretty gamma <$> eliminators)
instance (SysSyntax (Term sys) sys,
         Fine2Pretty sys (Mode sys), Fine2Pretty sys (Modality sys)) =>
         Show (Algorithm sys Void) where
  show alg = "[Algorithm|\n" ++ fine2string ScCtxEmpty alg omit ++ "\n|]"

instance (SysSyntax (Term sys) sys,
         Fine2Pretty sys (Mode sys), Fine2Pretty sys (Modality sys)) =>
         Fine2Pretty sys (Type sys) where
  fine2pretty gamma (Type t) opts = fine2pretty gamma t opts
deriving instance (SysSyntax (Term sys) sys,
                   Fine2Pretty sys (Mode sys), Fine2Pretty sys (Modality sys))
    => Show (Type sys Void)

nameWithIndex :: Maybe Raw.Name -> Nat -> PrettyTree String
nameWithIndex maybeName index = (fromMaybe (ribbon "_") $ Raw.unparse' <$> maybeName)
    |++ (toSubscript $ show $ index)

var2pretty :: DeBruijnLevel v => ScCtx sys v Void -> v -> Fine2PrettyOptions sys -> PrettyTree String
var2pretty gamma v opts = nameWithIndex (scGetName gamma v) (getDeBruijnLevel Proxy v)

{-| Never prints a solution instead.
    Term is required to be a meta.
-}
meta2pretty :: (DeBruijnLevel v,
                       SysSyntax (Term sys) sys,
                       Fine2Pretty sys (Mode sys), Fine2Pretty sys (Modality sys)) =>
  ScCtx sys v Void -> TermNV sys v -> Fine2PrettyOptions sys -> PrettyTree String
meta2pretty gamma tMeta@(TermMeta etaFlag meta (Compose depcies) (Compose maybeAlg)) opts =
  ribbon ("?" ++ show meta ++ (if etaFlag then "" else "-no-eta"))
  \\\ case maybeAlg of
        Nothing -> uglySubMeta
        Just alg -> if _fine2pretty'humanReadableMetas opts
                    then ["\x27ea" ++| fine2pretty gamma alg opts |++ "\x27eb"]
                    else uglySubMeta
  where uglySubMeta = (|++ "}") . (" .{" ++|) . ($ opts) . fine2pretty gamma <$> depcies
meta2pretty gamma t opts = unreachable

instance (SysSyntax (Term sys) sys,
         Fine2Pretty sys (Mode sys), Fine2Pretty sys (Modality sys)) =>
         Fine2Pretty sys (TermNV sys) where
  fine2pretty gamma (TermCons consTerm) opts = fine2pretty gamma consTerm opts
  fine2pretty gamma (TermElim mod eliminee tyEliminee eliminator) opts =
    elimination2pretty gamma mod eliminee tyEliminee eliminator opts
  fine2pretty gamma tMeta@(TermMeta etaFlag meta (Compose depcies) (Compose maybeAlg)) opts =
    case _fine2pretty'printSolutions opts of
      Nothing -> meta2pretty gamma tMeta opts
      Just solutions -> case lookup meta solutions of
        Nothing -> meta2pretty gamma tMeta opts
        Just (ForSomeDeBruijnLevel t) ->
          fine2pretty gamma (join $ (depcies !!) . fromIntegral . getDeBruijnLevel Proxy <$> t) opts
  fine2pretty gamma TermWildcard opts = ribbon "_"
  fine2pretty gamma (TermQName qname lookupresult) opts = Raw.unparse' qname
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
  fine2pretty gamma (TermAlgorithm alg result) opts = case _fine2pretty'printAlgorithm opts of
    PrintAlgorithm -> fine2pretty gamma alg opts |++ " \x2198 " |+| fine2pretty gamma result opts
    PrintAlgorithmUnderscore -> "_ \x2198 " ++| fine2pretty gamma result opts
    DontPrintAlgorithm -> fine2pretty gamma result opts
  {-fine2pretty gamma (TermSmartElim eliminee (Compose eliminators) result) opts =
    "(" ++| fine2pretty gamma eliminee opts |++ ")"
      |+| treeGroup ((" " ++|) . ($ opts) . fine2pretty gamma <$> eliminators)
      |++ " \x2198 " |+| fine2pretty gamma result opts
  fine2pretty gamma (TermGoal str result) opts =
    "?" ++ str ++ " \x2198 " ++| fine2pretty gamma result opts-}
  fine2pretty gamma (TermProblem t) opts = "(! " ++| fine2pretty gamma t opts |++ "!)"
instance (SysSyntax (Term sys) sys,
         Fine2Pretty sys (Mode sys), Fine2Pretty sys (Modality sys)) =>
         Show (TermNV sys Void) where
  show t = "[TermNV|\n" ++ fine2string ScCtxEmpty t omit ++ "\n|]"

toSubscript :: String -> String
toSubscript = map (\ char -> toEnum $ fromEnum char - 48 + 8320)

instance (SysSyntax (Term sys) sys,
         Fine2Pretty sys (Mode sys), Fine2Pretty sys (Modality sys), Fine2Pretty sys (termNV sys)) =>
         Fine2Pretty sys (Expr2 termNV sys) where
  fine2pretty gamma (Var2 v) opts = var2pretty gamma v opts
  fine2pretty gamma (Expr2 t) opts = fine2pretty gamma t opts
instance (SysSyntax (Term sys) sys,
         Fine2Pretty sys (Mode sys), Fine2Pretty sys (Modality sys), Fine2Pretty sys (termNV sys)) =>
         Show (Expr2 termNV sys Void) where
  show e = "[Expr2|\n" ++ fine2string ScCtxEmpty e omit ++ "\n|]"

----------------------

instance (SysSyntax (Term sys) sys,
         Fine2Pretty sys (Mode sys), Fine2Pretty sys (Modality sys)) =>
         Fine2Pretty sys (Annotation sys) where
  fine2pretty gamma (AnnotMode d) opts = fine2pretty gamma d opts
  fine2pretty gamma (AnnotModality mu) opts = fine2pretty gamma mu opts
  fine2pretty gamma (AnnotImplicit) opts = ribbon "~"
instance (SysSyntax (Term sys) sys,
         Fine2Pretty sys (Mode sys), Fine2Pretty sys (Modality sys)) =>
         Show (Annotation sys Void) where
  show annot = "[Annotation|\n" ++ fine2string ScCtxEmpty annot omit ++ "\n|]"

instance (SysSyntax (Term sys) sys,
         Fine2Pretty sys (Mode sys), Fine2Pretty sys (Modality sys)) =>
         Fine2Pretty sys (Plicity sys) where
  fine2pretty gamma Explicit opts = ribbonEmpty
  fine2pretty gamma Implicit opts = ribbon "~ | "
  fine2pretty gamma (Resolves t) opts = "resolves " ++| fine2pretty gamma t opts |++ " | "
instance (SysSyntax (Term sys) sys,
         Fine2Pretty sys (Mode sys), Fine2Pretty sys (Modality sys)) =>
         Show (Plicity sys Void) where
  show plic = "[Plicity|\n" ++ fine2string ScCtxEmpty plic omit ++ "\n|]"

declName2pretty :: forall v sys declSort . DeBruijnLevel v =>
  ScCtx sys v Void -> DeclName declSort -> Fine2PrettyOptions sys -> PrettyTree String
declName2pretty gamma (DeclNameVal name) opts = Raw.unparse' name
declName2pretty gamma (DeclNameModule str) opts = ribbon str
declName2pretty gamma (DeclNameSegment maybeName) opts =
  nameWithIndex maybeName (size (Proxy :: Proxy v))
declName2pretty gamma (DeclNameValSpec) opts = ribbon "<VALSPECNAME>"
instance Show (DeclName declSort) where
  show declName = "[DeclName|\n" ++ (render (declName2pretty ScCtxEmpty declName $? id) $? id) ++ "\n|]"

{-| Prettyprints a telescope. -}
telescope2pretties :: (DeBruijnLevel v,
         SysSyntax (Term sys) sys, Functor (ty sys),
         Fine2Pretty sys (Mode sys), Fine2Pretty sys (Modality sys), Fine2Pretty sys (ty sys)) =>
         ScCtx sys v Void -> Telescope ty sys v -> Fine2PrettyOptions sys -> [PrettyTree String]
telescope2pretties gamma (Telescoped Unit2) opts = []
telescope2pretties gamma (seg :|- telescope) opts =
  (fine2pretty gamma seg opts) : telescope2pretties (gamma ::.. (VarFromCtx <$> segment2scSegment seg)) telescope opts
telescope2pretties gamma (mu :** telescope) opts =
  [fine2pretty gamma (modality'mod mu) opts |++ " {" \\\
    telescope2pretties (() ::\\ gamma) telescope opts /+/
    ribbon "}"
  ]
instance (SysSyntax (Term sys) sys, Functor (ty sys),
         Fine2Pretty sys (Mode sys), Fine2Pretty sys (Modality sys), Fine2Pretty sys (ty sys)) =>
         Fine2Pretty sys (Telescope ty sys) where
  fine2pretty gamma telescope opts = treeGroup $ telescope2pretties gamma telescope opts
instance (SysSyntax (Term sys) sys, Functor (ty sys),
         Fine2Pretty sys (Mode sys), Fine2Pretty sys (Modality sys), Fine2Pretty sys (ty sys)) =>
         Show (Telescope ty sys Void) where
  show theta = "[Telescope|\n" ++ fine2string ScCtxEmpty theta omit ++ "\n|]"

declAnnots2pretties :: (DeBruijnLevel v,
         SysSyntax (Term sys) sys,
         Fine2Pretty sys (Mode sys), Fine2Pretty sys (Modality sys)) =>
         ScCtx sys v Void -> Declaration declSort content sys v -> Fine2PrettyOptions sys -> [PrettyTree String]
declAnnots2pretties gamma decl opts = [
                fine2pretty gamma (_decl'modty decl) opts,
                fine2pretty gamma (_decl'plicity decl) opts
              ]

{-
tdeclAnnots2pretties :: (SysSyntax (Term sys) sys, Functor (ty sys),
         Fine2Pretty sys (Mode sys), Fine2Pretty sys (Modality sys), Fine2Pretty sys ty) =>
         ScCtx sys v Void -> TelescopedDeclaration declSort ty content sys v -> [PrettyTree String]
tdeclAnnots2pretties gamma tdecl =
        getConst (mapTelescopedSc (
            \ wkn gammadelta decl -> Const $ declAnnots2pretties gammadelta decl
          ) gamma tdecl)
-}

seg2pretty ::
  (DeBruijnLevel v,
   SysSyntax (Term sys) sys, Functor (ty sys),
   Fine2Pretty sys (Mode sys), Fine2Pretty sys (Modality sys), Fine2Pretty sys (ty sys)) =>
   ScCtx sys v Void -> Segment ty sys v -> Nat ->
   Fine2PrettyOptions sys -> PrettyTree String
seg2pretty gamma seg index opts =
    ribbon " {" \\\
      prettyAnnots ///
    (nameWithIndex (_segment'name seg) index)
        |++ " : " |+| prettyType |++ "}"
    where
      prettyAnnots = declAnnots2pretties gamma seg opts
      prettyType = fine2pretty gamma (_decl'content seg) opts

dividedSeg2pretty :: forall v sys ty .
  (DeBruijnLevel v,
   Multimode sys, Functor (ty sys),
   Fine2Pretty sys (Mode sys), Fine2Pretty sys (Modality sys), Fine2Pretty sys (ty sys)) =>
   Maybe (ModedModality sys v) ->
   ScCtx sys v Void -> Segment ty sys v -> Nat ->
   Fine2PrettyOptions sys -> PrettyTree String
dividedSeg2pretty (Just dmu) gamma seg index opts = dividedSeg2pretty Nothing gamma seg' index opts
  where seg' = over decl'modty (divModedModality dmu) $ seg
dividedSeg2pretty Nothing gamma seg index opts = seg2pretty gamma seg index opts

instance (SysSyntax (Term sys) sys, Functor (ty sys),
         Fine2Pretty sys (Mode sys), Fine2Pretty sys (Modality sys), Fine2Pretty sys (ty sys)) =>
         Fine2Pretty sys (Segment ty sys) where
  fine2pretty gamma seg opts =
    seg2pretty gamma seg (size $ _scCtx'sizeProxy gamma) opts
instance (SysSyntax (Term sys) sys, Functor (ty sys),
         Fine2Pretty sys (Mode sys), Fine2Pretty sys (Modality sys), Fine2Pretty sys (ty sys)) =>
         Show (Segment ty sys Void) where
  show seg = "[Segment|\n" ++ fine2string ScCtxEmpty seg omit ++ "\n|]"

instance (SysSyntax (Term sys) sys,
         Fine2Pretty sys (Mode sys), Fine2Pretty sys (Modality sys)) =>
         Fine2Pretty sys (ValRHS sys) where
  fine2pretty gamma (ValRHS tm ty) opts = treeGroup [
      " : " ++| fine2pretty gamma ty opts,
      " = " ++| fine2pretty gamma tm opts
    ]
instance (SysSyntax (Term sys) sys,
         Fine2Pretty sys (Mode sys), Fine2Pretty sys (Modality sys)) =>
         Show (ValRHS sys Void) where
  show valRHS = "[ValRHS|\n" ++ fine2string ScCtxEmpty valRHS omit ++ "\n|]"

instance (SysSyntax (Term sys) sys,
         Fine2Pretty sys (Mode sys), Fine2Pretty sys (Modality sys)) =>
         Fine2Pretty sys (Val sys) where
  fine2pretty gamma val opts = case _fine2pretty'printEntry opts of
    PrintEntryName -> declName2pretty gamma (_decl'name val) opts
    PrintEntryNameAnnots -> prettyNameAndAnnots
    PrintEntryEntirely -> prettyNameAndAnnots
      \\\ telescope2pretties gamma (telescoped'telescope $ _decl'content val) opts
      /// prettyValRHS
    where
      prettyNameAndAnnots = ribbon "val ["
        \\\ declAnnots2pretties gamma val opts
        /// "] " ++| (declName2pretty gamma (_decl'name val) opts)
      prettyValRHS = 
        getConst (mapTelescopedScDB (
            \ wkn gammadelta t -> Const $ fine2pretty gammadelta t opts
          ) gamma $ _decl'content val)
instance (SysSyntax (Term sys) sys,
         Fine2Pretty sys (Mode sys), Fine2Pretty sys (Modality sys)) =>
         Show (Val sys Void) where
  show val = "[Val|\n" ++ fine2string ScCtxEmpty val omit ++ "\n|]"

moduleContents2pretty ::
  (SysSyntax (Term sys) sys, DeBruijnLevel v,
   Fine2Pretty sys (Mode sys), Fine2Pretty sys (Modality sys)) =>
  ScCtx sys v Void -> ModuleRHS sys v -> Fine2PrettyOptions sys -> [PrettyTree String]
moduleContents2pretty gamma moduleRHS opts = case unPrintModuleVerbosity $ _fine2pretty'printModule opts of
  Nothing -> [ribbon "..."]
  Just p ->
    (($ opts & fine2pretty'printEntry .~ p) .
     fine2pretty
     (gamma ::<...> (VarFromCtx <$> moduleRHS))
     <$> (reverse $ view moduleRHS'entries moduleRHS)
    ) >>= (\ entry -> case p of
              PrintEntryEntirely -> [entry, ribbon "        "]
              _ -> [entry |++ ", "]
          )
        
instance (SysSyntax (Term sys) sys,
         Fine2Pretty sys (Mode sys), Fine2Pretty sys (Modality sys)) =>
         Fine2Pretty sys (ModuleRHS sys) where
  fine2pretty gamma moduleRHS opts = ribbon " where {"
    \\\ moduleContents2pretty gamma moduleRHS opts
    /// ribbon "}"
instance (SysSyntax (Term sys) sys,
         Fine2Pretty sys (Mode sys), Fine2Pretty sys (Modality sys)) =>
         Show (ModuleRHS sys Void) where
  show moduleRHS = "[ModuleRHS|\n" ++ fine2string ScCtxEmpty moduleRHS omit ++ "\n|]"

instance (SysSyntax (Term sys) sys,
         Fine2Pretty sys (Mode sys), Fine2Pretty sys (Modality sys)) =>
         Fine2Pretty sys (Module sys) where
  fine2pretty gamma modul opts = case _fine2pretty'printEntry opts of
    PrintEntryName -> declName2pretty gamma (_decl'name modul) opts
    PrintEntryNameAnnots -> prettyNameAndAnnots
    PrintEntryEntirely -> prettyNameAndAnnots
      \\\ telescope2pretties gamma (telescoped'telescope $ _decl'content modul) opts
      /// prettyModuleRHS
    where
      prettyNameAndAnnots = ribbon "module  ["
        \\\ declAnnots2pretties gamma modul opts
        /// "] " ++| (declName2pretty gamma (_decl'name modul) opts)
      prettyModuleRHS = 
        getConst (mapTelescopedScDB (
            \ wkn gammadelta modulRHS -> Const $ fine2pretty gammadelta modulRHS opts
          ) gamma $ _decl'content modul)
instance (SysSyntax (Term sys) sys,
         Fine2Pretty sys (Mode sys), Fine2Pretty sys (Modality sys)) =>
         Show (Module sys Void) where
  show modul = "[Module|\n" ++ fine2string ScCtxEmpty modul omit ++ "\n|]"

instance (SysSyntax (Term sys) sys,
         Fine2Pretty sys (Mode sys), Fine2Pretty sys (Modality sys)) =>
         Fine2Pretty sys (Entry sys) where
  fine2pretty gamma (EntryVal val) opts = fine2pretty gamma val opts
  fine2pretty gamma (EntryModule modul) opts = fine2pretty gamma modul opts
instance (SysSyntax (Term sys) sys,
         Fine2Pretty sys (Mode sys), Fine2Pretty sys (Modality sys)) =>
         Show (Entry sys Void) where
  show entry = "[Entry|\n" ++ fine2string ScCtxEmpty entry omit ++ "\n|]"

instance (SysSyntax (Term sys) sys, Functor (ty sys),
         Fine2Pretty sys (Mode sys), Fine2Pretty sys (Modality sys), Fine2Pretty sys (ty sys)) =>
         Fine2Pretty sys (Twice2 ty sys) where
  fine2pretty gamma (Twice2 ty1 ty2) opts =
    ribbonEmpty \\\ [fine2pretty gamma ty1 opts, ribbon " =[]= ", fine2pretty gamma ty2 opts]
