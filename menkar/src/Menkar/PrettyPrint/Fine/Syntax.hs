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
import Data.Omissible

import Data.Void
import Data.Maybe
import Data.Proxy
import Control.Exception.AssertFalse
import Data.Functor.Compose
import Data.Functor.Const
import Control.Lens

charYielding :: Char
charYielding = '\x2198'

data FineAlgorithmOptions = FineAlgorithmOptions {
  -- | Print goal / smart elimination as its result.
  _fineAlgorithm'suppressAltogether :: Bool,
  -- | Do not explicitly view goal / smart elimination.
  -- | (Only relevant if @'_fineAlgorithm'suppressAltogether'@ is @False@.)
  _fineAlgorithm'suppressAlgorithm :: Bool
  }

instance Omissible FineAlgorithmOptions where
  omit = FineAlgorithmOptions True True

data Fine2PrettyOptions sys = Fine2PrettyOptions {
  -- | How to render.
  _finePretty'renderOptions :: RenderOptions,
  -- | Instead of listing all dependencies, plug them into the smart elimination / ... being resolved.
  _finePretty'humanReadableMetas :: Bool,
  _finePretty'smartElimOptions :: FineAlgorithmOptions,
  _finePretty'goalOptions :: FineAlgorithmOptions,
  -- | When printing a solved meta, print its solution instead.
  _finePretty'printSolutions :: Maybe (ForSomeDeBruijnLevel (Term sys)),
  -- | When printing contexts, explicity print left divisions, rather than computing the divided
  -- | modality.
  _finePretty'explicitLeftDivision :: Bool
  }

makeLenses ''Fine2PrettyOptions
makeLenses ''FineAlgorithmOptions

instance Omissible (Fine2PrettyOptions sys) where
  omit = Fine2PrettyOptions
    omit
    True
    omit
    omit
    Nothing
    True

---------------------------

class Fine2Pretty sys t | t -> sys where
  fine2pretty :: DeBruijnLevel v => ScCtx sys v Void -> t v -> Fine2PrettyOptions sys -> PrettyTree String
  fine2string :: DeBruijnLevel v => ScCtx sys v Void -> t v -> Fine2PrettyOptions sys -> String
  fine2string gamma x opts = render (fine2pretty gamma x opts) $ _finePretty'renderOptions opts

---------------------------

instance (SysTrav sys,
          Fine2Pretty sys (Mode sys), Fine2Pretty sys (Modality sys)) =>
         Fine2Pretty sys (ModedModality sys) where
  fine2pretty gamma (ModedModality d mu) opts = ribbonEmpty \\\ [
                "d " ++| fine2pretty gamma d opts |++ " | ",
                "m " ++| fine2pretty gamma mu opts |++ " | "
              ]
instance (SysTrav sys,
          Fine2Pretty sys (Mode sys), Fine2Pretty sys (Modality sys)) =>
         Show (ModedModality sys Void) where
  show dmu = "[ModedModality|\n" ++ fine2string ScCtxEmpty dmu omit ++ "\n|]"

deriving instance (Show (Mode sys v), Show (Modality sys v)) => Show (ModedContramodality sys v)

binding2pretty :: (DeBruijnLevel v,
                  SysTrav sys,
                  Fine2Pretty sys (Mode sys), Fine2Pretty sys (Modality sys), Fine2Pretty sys (rhs sys)) =>
                  String -> ScCtx sys v Void -> Binding Type rhs sys v -> Fine2PrettyOptions sys -> PrettyTree String
binding2pretty opstring gamma binding opts =
  fine2pretty gamma (binding'segment binding) opts
  \\\ [" " ++ opstring ++ " " ++|
       fine2pretty (gamma ::.. (VarFromCtx <$> segment2scSegment (binding'segment binding))) (binding'body binding) opts
      ]
instance (SysTrav sys,
         Fine2Pretty sys (Mode sys), Fine2Pretty sys (Modality sys), Fine2Pretty sys (rhs sys)) =>
         Fine2Pretty sys (Binding Type rhs sys) where
  fine2pretty gamma binding opts = binding2pretty ">" gamma binding opts
instance (SysTrav sys,
         Fine2Pretty sys (Mode sys), Fine2Pretty sys (Modality sys), Fine2Pretty sys (rhs sys)) =>
         Show (Binding Type rhs sys Void) where
  show binding = "[Binding|\n" ++ fine2string ScCtxEmpty binding omit ++ "\n|]"

instance (SysTrav sys,
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
instance (SysTrav sys,
         Fine2Pretty sys (Mode sys), Fine2Pretty sys (Modality sys)) =>
         Show (UniHSConstructor sys Void) where
  show typeterm = "[UniHSConstructor|\n" ++ fine2string ScCtxEmpty typeterm omit ++ "\n|]"
  
instance (SysTrav sys,
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
instance (SysTrav sys,
         Fine2Pretty sys (Mode sys), Fine2Pretty sys (Modality sys)) =>
         Show (ConstructorTerm sys Void) where
  show consTerm = "[ConstructorTerm|\n" ++ fine2string ScCtxEmpty consTerm omit ++ "\n|]"

instance (SysTrav sys,
         Fine2Pretty sys (Mode sys), Fine2Pretty sys (Modality sys)) =>
         Fine2Pretty sys (SmartEliminator sys) where
  fine2pretty gamma (SmartElimDots) opts = ribbon "..."
  --fine2pretty gamma (SmartElimEnd argSpec) = Raw.unparse' (Raw.ElimEnd argSpec)
  fine2pretty gamma (SmartElimArg Raw.ArgSpecNext term) opts = ".{" ++| fine2pretty gamma term opts |++ "}"
  fine2pretty gamma (SmartElimArg Raw.ArgSpecExplicit term) opts = "(" ++| fine2pretty gamma term opts |++ ")"
  fine2pretty gamma (SmartElimArg (Raw.ArgSpecNamed name) term) opts =
    ".{" ++ Raw.unparse name ++ " = " ++| fine2pretty gamma term opts |++ "}"
  fine2pretty gamma (SmartElimProj projSpec) opts = Raw.unparse' (Raw.ElimProj projSpec)
instance (SysTrav sys,
         Fine2Pretty sys (Mode sys), Fine2Pretty sys (Modality sys)) =>
         Show (SmartEliminator sys Void) where
  show smartElim = "[SmartEliminator|\n" ++ fine2string ScCtxEmpty smartElim omit ++ "\n|]"

typed2pretty :: (DeBruijnLevel v,
                       SysTrav sys,
                       Fine2Pretty sys (Mode sys), Fine2Pretty sys (Modality sys)) =>
  ScCtx sys v Void ->
  Term sys v ->
  Type sys v ->
  Fine2PrettyOptions sys ->
  PrettyTree String
typed2pretty gamma t ty opts = fine2pretty gamma t opts
{-  ribbon "(ofType" \\\ [
      " (" ++| fine2pretty gamma ty opts |++ ")",
      " (" ++| fine2pretty gamma t opts |++ ")"
    ] ///
  ribbon ")" -}

instance (SysTrav sys,
         Fine2Pretty sys (Mode sys), Fine2Pretty sys (Modality sys), Fine2Pretty sys (rhs sys)) =>
         Fine2Pretty sys (NamedBinding rhs sys) where
  fine2pretty gamma (NamedBinding maybeName body) opts =
    let gammaExt = gamma ::.. ScSegment maybeName
    in  var2pretty gammaExt VarLast opts |++ " > " |+| fine2pretty gammaExt body opts
instance (SysTrav sys,
         Fine2Pretty sys (Mode sys), Fine2Pretty sys (Modality sys), Fine2Pretty sys (rhs sys)) =>
         Show (NamedBinding rhs sys Void) where
  show binding = "[NamedBinding|\n" ++ fine2string ScCtxEmpty binding omit ++ "\n|]"

elimination2pretty :: (DeBruijnLevel v,
                       SysTrav sys,
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
    "(" ++| typed2pretty gamma eliminee (Type $ Expr2 $ TermCons $ ConsUniHS $ tyEliminee) opts |++ ")" \\\
      [
      " .{" ++| fine2pretty gamma arg opts |++ "}"
      ]
elimination2pretty gamma dmu eliminee tyEliminee (Fst) opts =
  "(" ++| typed2pretty gamma eliminee (Type $ Expr2 $ TermCons $ ConsUniHS $ tyEliminee) opts |++ ") .1 "
elimination2pretty gamma dmu eliminee tyEliminee (Snd) opts =
  "(" ++| typed2pretty gamma eliminee (Type $ Expr2 $ TermCons $ ConsUniHS $ tyEliminee) opts |++ ") ..2 "
elimination2pretty gamma dmu eliminee tyEliminee (Unbox) opts =
  "unbox (" ++| typed2pretty gamma eliminee (Type $ Expr2 $ TermCons $ ConsUniHS $ tyEliminee) opts |++ ") "
elimination2pretty gamma dmu eliminee tyEliminee (Funext) opts =
  "funext (" ++| typed2pretty gamma eliminee (Type $ Expr2 $ TermCons $ ConsUniHS $ tyEliminee) opts |++ ") "
elimination2pretty gamma dmu eliminee tyEliminee (ElimDep motive (ElimSigma clausePair)) opts =
  ribbon "indSigma " \\\ [
      fine2pretty gamma dmu opts,
      "(" ++| fine2pretty gamma motive opts |++ ") ",
      "(" ++| fine2pretty gamma clausePair opts |++ ") ",
      "(" ++| typed2pretty gamma eliminee (Type $ Expr2 $ TermCons $ ConsUniHS $ tyEliminee) opts |++ ") "
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
elimination2pretty gamma dmu eliminee tyEliminee (ElimDep motive (ElimBox clauseBox)) opts =
  ribbon "indBox " \\\ [
      fine2pretty gamma dmu opts,
      "(" ++| fine2pretty gamma motive opts |++ ") ",
      "(" ++| fine2pretty gamma clauseBox opts |++ ") ",
      "(" ++| typed2pretty gamma eliminee (Type $ Expr2 $ TermCons $ ConsUniHS $ tyEliminee) opts |++ ") "
    ]
elimination2pretty gamma dmu eliminee tyEliminee (ElimDep motive (ElimEmpty)) opts =
  ribbon "indEmpty " \\\ [
      fine2pretty gamma dmu opts,
      "(" ++| fine2pretty gamma motive opts |++ ") ",
      "(" ++| typed2pretty gamma eliminee (Type $ Expr2 $ TermCons $ ConsUniHS $ tyEliminee) opts |++ ") "
    ]
elimination2pretty gamma dmu eliminee tyEliminee (ElimDep motive (ElimNat clauseZero clauseSuc)) opts =
  ribbon "indNat " \\\ [
      fine2pretty gamma dmu opts,
      "(" ++| fine2pretty gamma motive opts |++ ") ",
      "(" ++| fine2pretty gamma clauseZero opts |++ ") ",
      "(" ++| fine2pretty gamma clauseSuc opts |++ ") ",
      "(" ++| typed2pretty gamma eliminee (Type $ Expr2 $ TermCons $ ConsUniHS $ tyEliminee) opts |++ ") "
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
instance (SysTrav sys,
         Fine2Pretty sys (Mode sys), Fine2Pretty sys (Modality sys)) =>
         Show (Eliminator sys Void) where
  show elim = "[Eliminator| x > " ++ render defaultRenderState (elimination2pretty ScCtxEmpty (ribbon "x") elim)
-}

instance (SysTrav sys,
         Fine2Pretty sys (Mode sys), Fine2Pretty sys (Modality sys)) =>
         Fine2Pretty sys (Type sys) where
  fine2pretty gamma (Type t) opts = fine2pretty gamma t opts
deriving instance (SysTrav sys,
                   Fine2Pretty sys (Mode sys), Fine2Pretty sys (Modality sys))
    => Show (Type sys Void)

var2pretty :: DeBruijnLevel v => ScCtx sys v Void -> v -> Fine2PrettyOptions sys -> PrettyTree String
var2pretty gamma v opts = (fromMaybe (ribbon "_") $ Raw.unparse' <$> scGetName gamma v)
    |++ (toSubscript $ show $ getDeBruijnLevel Proxy v)

instance (SysTrav sys,
         Fine2Pretty sys (Mode sys), Fine2Pretty sys (Modality sys)) =>
         Fine2Pretty sys (TermNV sys) where
  fine2pretty gamma (TermCons consTerm) opts = fine2pretty gamma consTerm opts
  fine2pretty gamma (TermElim mod eliminee tyEliminee eliminator) opts =
    elimination2pretty gamma mod eliminee tyEliminee eliminator opts
  fine2pretty gamma (TermMeta etaFlag i (Compose depcies)) opts =
    ribbon ("?" ++ show i ++ (if etaFlag then "" else "-no-eta"))
    \\\ ((|++ "}") . (" .{" ++|) . ($ opts) . fine2pretty gamma <$> depcies)
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
  fine2pretty gamma (TermSmartElim eliminee (Compose eliminators) result) opts =
    "(" ++| fine2pretty gamma eliminee opts |++ ")"
      |+| treeGroup ((" " ++|) . ($ opts) . fine2pretty gamma <$> eliminators)
      |++ " \x2198 " |+| fine2pretty gamma result opts
  fine2pretty gamma (TermGoal str result) opts =
    "?" ++ str ++ " \x2198 " ++| fine2pretty gamma result opts
  fine2pretty gamma (TermProblem t) opts = "(! " ++| fine2pretty gamma t opts |++ "!)"
instance (SysTrav sys,
         Fine2Pretty sys (Mode sys), Fine2Pretty sys (Modality sys)) =>
         Show (TermNV sys Void) where
  show t = "[TermNV|\n" ++ fine2string ScCtxEmpty t omit ++ "\n|]"

toSubscript :: String -> String
toSubscript = map (\ char -> toEnum $ fromEnum char - 48 + 8320)

instance (SysTrav sys,
         Fine2Pretty sys (Mode sys), Fine2Pretty sys (Modality sys), Fine2Pretty sys (termNV sys)) =>
         Fine2Pretty sys (Expr2 termNV sys) where
  fine2pretty gamma (Var2 v) opts = var2pretty gamma v opts
  fine2pretty gamma (Expr2 t) opts = fine2pretty gamma t opts
instance (SysTrav sys,
         Fine2Pretty sys (Mode sys), Fine2Pretty sys (Modality sys), Fine2Pretty sys (termNV sys)) =>
         Show (Expr2 termNV sys Void) where
  show e = "[Expr2|\n" ++ fine2string ScCtxEmpty e omit ++ "\n|]"

----------------------

instance (SysTrav sys,
         Fine2Pretty sys (Mode sys), Fine2Pretty sys (Modality sys)) =>
         Fine2Pretty sys (Annotation sys) where
  fine2pretty gamma (AnnotMode d) opts = fine2pretty gamma d opts
  fine2pretty gamma (AnnotModality mu) opts = fine2pretty gamma mu opts
  fine2pretty gamma (AnnotImplicit) opts = ribbon "~"
instance (SysTrav sys,
         Fine2Pretty sys (Mode sys), Fine2Pretty sys (Modality sys)) =>
         Show (Annotation sys Void) where
  show annot = "[Annotation|\n" ++ fine2string ScCtxEmpty annot omit ++ "\n|]"

instance (SysTrav sys,
         Fine2Pretty sys (Mode sys), Fine2Pretty sys (Modality sys)) =>
         Fine2Pretty sys (Plicity sys) where
  fine2pretty gamma Explicit opts = ribbonEmpty
  fine2pretty gamma Implicit opts = ribbon "~ | "
  fine2pretty gamma (Resolves t) opts = "resolves " ++| fine2pretty gamma t opts |++ " | "
instance (SysTrav sys,
         Fine2Pretty sys (Mode sys), Fine2Pretty sys (Modality sys)) =>
         Show (Plicity sys Void) where
  show plic = "[Plicity|\n" ++ fine2string ScCtxEmpty plic omit ++ "\n|]"

declName2pretty :: forall v sys declSort . DeBruijnLevel v =>
  ScCtx sys v Void -> DeclName declSort -> Fine2PrettyOptions sys -> PrettyTree String
declName2pretty gamma (DeclNameVal name) opts = Raw.unparse' name
declName2pretty gamma (DeclNameModule str) opts = ribbon str
declName2pretty gamma (DeclNameSegment maybeName) opts = (fromMaybe (ribbon "_") $ Raw.unparse' <$> maybeName)
                                              |++ (toSubscript $ show $ size (Proxy :: Proxy v))
declName2pretty gamma (DeclNameValSpec) opts = ribbon "<VALSPECNAME>"
instance Show (DeclName declSort) where
  show declName = "[DeclName|\n" ++ (render (declName2pretty ScCtxEmpty declName $? id) $? id) ++ "\n|]"

{-| Prettyprints a telescope. -}
telescope2pretties :: (DeBruijnLevel v,
         SysTrav sys, Functor (ty sys),
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
instance (SysTrav sys, Functor (ty sys),
         Fine2Pretty sys (Mode sys), Fine2Pretty sys (Modality sys), Fine2Pretty sys (ty sys)) =>
         Fine2Pretty sys (Telescope ty sys) where
  fine2pretty gamma telescope opts = treeGroup $ telescope2pretties gamma telescope opts
instance (SysTrav sys, Functor (ty sys),
         Fine2Pretty sys (Mode sys), Fine2Pretty sys (Modality sys), Fine2Pretty sys (ty sys)) =>
         Show (Telescope ty sys Void) where
  show theta = "[Telescope|\n" ++ fine2string ScCtxEmpty theta omit ++ "\n|]"

declAnnots2pretties :: (DeBruijnLevel v,
         SysTrav sys,
         Fine2Pretty sys (Mode sys), Fine2Pretty sys (Modality sys)) =>
         ScCtx sys v Void -> Declaration declSort content sys v -> Fine2PrettyOptions sys -> [PrettyTree String]
declAnnots2pretties gamma decl opts = [
                fine2pretty gamma (_decl'modty decl) opts,
                fine2pretty gamma (_decl'plicity decl) opts
              ]

{-
tdeclAnnots2pretties :: (SysTrav sys, Functor (ty sys),
         Fine2Pretty sys (Mode sys), Fine2Pretty sys (Modality sys), Fine2Pretty sys ty) =>
         ScCtx sys v Void -> TelescopedDeclaration declSort ty content sys v -> [PrettyTree String]
tdeclAnnots2pretties gamma tdecl =
        getConst (mapTelescopedSc (
            \ wkn gammadelta decl -> Const $ declAnnots2pretties gammadelta decl
          ) gamma tdecl)
-}

instance (SysTrav sys, Functor (ty sys),
         Fine2Pretty sys (Mode sys), Fine2Pretty sys (Modality sys), Fine2Pretty sys (ty sys)) =>
         Fine2Pretty sys (Segment ty sys) where
  fine2pretty gamma seg opts = ribbon " {" \\\
    prettyAnnots ///
    (declName2pretty gamma (DeclNameSegment $ _segment'name seg) opts) |++ " : " |+| prettyType |++ "}"
    where
      prettyAnnots = declAnnots2pretties gamma seg opts
      prettyType = fine2pretty gamma (_decl'content seg) opts
instance (SysTrav sys, Functor (ty sys),
         Fine2Pretty sys (Mode sys), Fine2Pretty sys (Modality sys), Fine2Pretty sys (ty sys)) =>
         Show (Segment ty sys Void) where
  show seg = "[Segment|\n" ++ fine2string ScCtxEmpty seg omit ++ "\n|]"

instance (SysTrav sys,
         Fine2Pretty sys (Mode sys), Fine2Pretty sys (Modality sys)) =>
         Fine2Pretty sys (ValRHS sys) where
  fine2pretty gamma (ValRHS tm ty) opts = treeGroup [
      " : " ++| fine2pretty gamma ty opts,
      " = " ++| fine2pretty gamma tm opts
    ]
instance (SysTrav sys,
         Fine2Pretty sys (Mode sys), Fine2Pretty sys (Modality sys)) =>
         Show (ValRHS sys Void) where
  show valRHS = "[ValRHS|\n" ++ fine2string ScCtxEmpty valRHS omit ++ "\n|]"

instance (SysTrav sys,
         Fine2Pretty sys (Mode sys), Fine2Pretty sys (Modality sys)) =>
         Fine2Pretty sys (Val sys) where
  fine2pretty gamma val opts =
    ribbon "val ["
    \\\ declAnnots2pretties gamma val opts
    /// "] " ++| (declName2pretty gamma (_decl'name val) opts)
    \\\ telescope2pretties gamma (telescoped'telescope $ _decl'content val) opts
    /// prettyValRHS
    where
      prettyValRHS = 
        getConst (mapTelescopedScDB (
            \ wkn gammadelta t -> Const $ fine2pretty gammadelta t opts
          ) gamma $ _decl'content val)
instance (SysTrav sys,
         Fine2Pretty sys (Mode sys), Fine2Pretty sys (Modality sys)) =>
         Show (Val sys Void) where
  show val = "[Val|\n" ++ fine2string ScCtxEmpty val omit ++ "\n|]"
        
instance (SysTrav sys,
         Fine2Pretty sys (Mode sys), Fine2Pretty sys (Modality sys)) =>
         Fine2Pretty sys (ModuleRHS sys) where
  fine2pretty gamma moduleRHS opts = ribbon " where {"
    \\\ ((($ opts) . fine2pretty (gamma ::<...> (VarFromCtx <$> moduleRHS)) <$> (reverse $ view moduleRHS'entries moduleRHS))
          >>= (\ entry -> [entry, ribbon "        "]))
    /// ribbon "}"
instance (SysTrav sys,
         Fine2Pretty sys (Mode sys), Fine2Pretty sys (Modality sys)) =>
         Show (ModuleRHS sys Void) where
  show moduleRHS = "[ModuleRHS|\n" ++ fine2string ScCtxEmpty moduleRHS omit ++ "\n|]"

instance (SysTrav sys,
         Fine2Pretty sys (Mode sys), Fine2Pretty sys (Modality sys)) =>
         Fine2Pretty sys (Module sys) where
  fine2pretty gamma modul opts =
    ribbon "module  ["
    \\\ declAnnots2pretties gamma modul opts
    /// "] " ++| (declName2pretty gamma (_decl'name modul) opts)
    \\\ telescope2pretties gamma (telescoped'telescope $ _decl'content modul) opts
    /// prettyModuleRHS
    where
      prettyModuleRHS = 
        getConst (mapTelescopedScDB (
            \ wkn gammadelta modulRHS -> Const $ fine2pretty gammadelta modulRHS opts
          ) gamma $ _decl'content modul)
instance (SysTrav sys,
         Fine2Pretty sys (Mode sys), Fine2Pretty sys (Modality sys)) =>
         Show (Module sys Void) where
  show modul = "[Module|\n" ++ fine2string ScCtxEmpty modul omit ++ "\n|]"

instance (SysTrav sys,
         Fine2Pretty sys (Mode sys), Fine2Pretty sys (Modality sys)) =>
         Fine2Pretty sys (Entry sys) where
  fine2pretty gamma (EntryVal val) opts = fine2pretty gamma val opts
  fine2pretty gamma (EntryModule modul) opts = fine2pretty gamma modul opts
instance (SysTrav sys,
         Fine2Pretty sys (Mode sys), Fine2Pretty sys (Modality sys)) =>
         Show (Entry sys Void) where
  show entry = "[Entry|\n" ++ fine2string ScCtxEmpty entry omit ++ "\n|]"

instance (SysTrav sys, Functor (ty sys),
         Fine2Pretty sys (Mode sys), Fine2Pretty sys (Modality sys), Fine2Pretty sys (ty sys)) =>
         Fine2Pretty sys (Twice2 ty sys) where
  fine2pretty gamma (Twice2 ty1 ty2) opts =
    ribbonEmpty \\\ [fine2pretty gamma ty1 opts, ribbon " =[]= ", fine2pretty gamma ty2 opts]
