{-# LANGUAGE UndecidableInstances #-}

module Menkar.PrettyPrint.Fine.Syntax where

import Prelude hiding (lookup)

import Menkar.PrettyPrint.Fine.Class
import Menkar.System.PrettyPrint
import Menkar.System.Fine
import Menkar.Fine.Syntax
import Menkar.Basic.Context
import Menkar.Fine.Context
import Menkar.PrettyPrint.Aux.Context
import Menkar.Fine.LookupQName
import qualified Menkar.Raw as Raw
import qualified Menkar.PrettyPrint.Raw as Raw

import Text.PrettyPrint.Tree
import Data.Omissible
import Data.Functor.Functor1

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
import GHC.Generics

charYielding :: Char
charYielding = '\x2198'

---------------------------
{-
instance (SysFinePretty sys,
          Fine2Pretty sys (Mode sys), Fine2Pretty sys (Modality sys)) =>
          Fine2Pretty sys (ModedModality sys) where
  fine2pretty gamma (ModedModality dom cod mu) opts = ribbonEmpty \\\ [
                "d " ++| fine2pretty gamma dom opts |++ " | ",
                "m " ++| fine2pretty gamma mu opts |++ " | "
                -- todo add cod
              ]
instance (SysFinePretty sys,
          Fine2Pretty sys (Mode sys), Fine2Pretty sys (Modality sys)) =>
         Show (ModedModality sys Void) where
  show dmu = "[ModedModality|\n" ++ fine2string @sys ScCtxEmpty dmu omit ++ "\n|]"

instance (SysFinePretty sys,
          Fine2Pretty sys (Mode sys), Fine2Pretty sys (Modality sys)) =>
          Fine2Pretty sys (ModedDegree sys) where
  fine2pretty gamma (ModedDegree d deg) opts = fine2pretty gamma deg opts
-}
--deriving instance (Show (Mode sys v), Show (Modality sys v)) => Show (ModedContramodality sys v)

binding2pretty :: (DeBruijnLevel v,
                  SysFinePretty sys,
                  Fine2Pretty sys (Mode sys), Fine2Pretty sys (Modality sys), Fine2Pretty sys (rhs sys)) =>
                  String -> ScCtx sys v Void -> Binding Type rhs sys v -> Fine2PrettyOptions sys -> PrettyTree String
binding2pretty opstring gamma binding opts =
  fine2pretty gamma (binding'segment binding) opts
  \\\ [" " ++ opstring ++ " " ++|
       fine2pretty (gamma ::.. (VarFromCtx <$> segment2scSegment (binding'segment binding))) (binding'body binding) opts
      ]
instance (SysFinePretty sys,
         Fine2Pretty sys (Mode sys), Fine2Pretty sys (Modality sys), Fine2Pretty sys (rhs sys)) =>
         Fine2Pretty sys (Binding Type rhs sys) where
  fine2pretty gamma binding opts = binding2pretty ">" gamma binding opts
instance (SysFinePretty sys,
         Fine2Pretty sys (Mode sys), Fine2Pretty sys (Modality sys), Fine2Pretty sys (rhs sys)) =>
         Show (Binding Type rhs sys Void) where
  show binding = "[Binding|\n" ++ fine2string @sys ScCtxEmpty binding omit ++ "\n|]"

instance (SysFinePretty sys,
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
  fine2pretty gamma (BoxType tySeg) opts = --"Box" ++| fine2pretty gamma tySeg opts
    "{" ++| fine2pretty gamma (_segment'modty tySeg) opts |++ "} -> " |+| fine2pretty gamma (_segment'content tySeg) opts
  fine2pretty gamma (NatType) opts = ribbon "Nat"
  fine2pretty gamma (EqType tyAmbient tyL tyR) opts =
    ribbonEmpty
    \\\ ["(" ++| fine2pretty gamma tyL opts |++ ")"]
    /+/ " == .{" ++| fine2pretty gamma tyAmbient opts |++ "} "
    \\\ ["(" ++| fine2pretty gamma tyR opts |++ ")"]
  fine2pretty gamma (SysType sysType) opts = fine2pretty gamma sysType opts
instance (SysFinePretty sys,
         Fine2Pretty sys (Mode sys), Fine2Pretty sys (Modality sys)) =>
         Show (UniHSConstructor sys Void) where
  show typeterm = "[UniHSConstructor|\n" ++ fine2string @sys ScCtxEmpty typeterm omit ++ "\n|]"
  
instance (SysFinePretty sys,
         Fine2Pretty sys (Mode sys), Fine2Pretty sys (Modality sys)) =>
         Fine2Pretty sys (ConstructorTerm sys) where
  fine2pretty gamma (ConsUniHS typeterm) opts = fine2pretty gamma typeterm opts
    {-ribbon "withMode" \\\ [
      " " ++| fine2pretty gamma (Mode d),
      " (" ++| fine2pretty gamma typeterm |++ ")"
      ]-}
  fine2pretty gamma (Lam (Binding seg (ValRHS body cod))) opts =
    binding2pretty ">" gamma (Binding seg $ TypedTerm body cod) opts
  fine2pretty gamma (Pair binding tmFst tmSnd) opts =
    ribbon "ofType" \\\ [
      " (" ++| fine2pretty gamma (Sigma binding) opts |++ ")",
      " (" ++| fine2pretty gamma tmFst opts |++ " , " |+| fine2pretty gamma tmSnd opts |++ ")"
      ]
  fine2pretty gamma ConsUnit opts = ribbon "unit"
  fine2pretty gamma (ConsBox tySeg tmUnbox) opts = "{} > " ++| fine2pretty gamma tmUnbox opts
    {-ribbon "ofType" \\\ [
      " (" ++| fine2pretty gamma (BoxType tySeg) opts |++ ")",
      " (box .{" ++| fine2pretty gamma tmUnbox opts |++ "})"
      ]-}
  fine2pretty gamma (ConsZero) opts = ribbon "zero"
  fine2pretty gamma (ConsSuc t) opts = "suc .{" ++| fine2pretty gamma t opts |++ "}"
  fine2pretty gamma (ConsRefl tyAmbient t) opts = "refl .{" ++| typed2pretty gamma t tyAmbient opts |++ "}"
instance (SysFinePretty sys,
         Fine2Pretty sys (Mode sys), Fine2Pretty sys (Modality sys)) =>
         Show (ConstructorTerm sys Void) where
  show consTerm = "[ConstructorTerm|\n" ++ fine2string @sys ScCtxEmpty consTerm omit ++ "\n|]"

instance (SysFinePretty sys,
         Fine2Pretty sys (Mode sys), Fine2Pretty sys (Modality sys)) =>
         Fine2Pretty sys (SmartEliminator sys) where
  fine2pretty gamma (SmartElimDots) opts = ribbon "..."
  --fine2pretty gamma (SmartElimEnd argSpec) = Raw.unparse' (Raw.ElimEnd argSpec)
  fine2pretty gamma (SmartElimArg Raw.ArgSpecNext dmu term) opts =
    ".{" ++| fine2pretty gamma dmu opts |+| fine2pretty gamma term opts |++ "}"
  fine2pretty gamma (SmartElimArg Raw.ArgSpecExplicit dmu term) opts =
    "(" ++| fine2pretty gamma dmu opts |++ " | " |+| fine2pretty gamma term opts |++ ")"
  fine2pretty gamma (SmartElimArg (Raw.ArgSpecNamed name) dmu term) opts =
    ".{" ++| fine2pretty gamma dmu opts |++ " | " |++ Raw.unparse name ++ " = " |+| fine2pretty gamma term opts |++ "}"
  fine2pretty gamma (SmartElimProj projSpec) opts = Raw.unparse' projSpec
  fine2pretty gamma (SmartElimUnbox) opts = ribbon ".{}"
instance (SysFinePretty sys,
         Fine2Pretty sys (Mode sys), Fine2Pretty sys (Modality sys)) =>
         Show (SmartEliminator sys Void) where
  show smartElim = "[SmartEliminator|\n" ++ fine2string @sys ScCtxEmpty smartElim omit ++ "\n|]"

typed2pretty' ::
  PrettyTree String ->
  PrettyTree String ->
  Fine2PrettyOptions sys ->
  PrettyTree String
typed2pretty' tPretty tyPretty opts
  | _fine2pretty'printTypeAnnotations opts =
    ribbon "(ofType" \\\ [
          " (" ++| tyPretty |++ ")",
          " (" ++| tPretty |++ ")"
        ] ///
      ribbon ")"
  | otherwise = tPretty
  
typed2pretty :: (DeBruijnLevel v,
                       SysFinePretty sys,
                       Fine2Pretty sys (Mode sys), Fine2Pretty sys (Modality sys)) =>
  ScCtx sys v Void ->
  Term sys v ->
  Type sys v ->
  Fine2PrettyOptions sys ->
  PrettyTree String
typed2pretty gamma t ty opts = typed2pretty' (fine2pretty gamma t opts) (fine2pretty gamma ty opts) opts

data TypedTerm sys v = TypedTerm (Term sys v) (Type sys v)
instance (SysFinePretty sys,
         Fine2Pretty sys (Mode sys), Fine2Pretty sys (Modality sys)) =>
         Fine2Pretty sys (TypedTerm sys) where
  fine2pretty gamma (TypedTerm t ty) opts = typed2pretty gamma t ty opts

instance (SysFinePretty sys,
         Fine2Pretty sys (Mode sys), Fine2Pretty sys (Modality sys), Fine2Pretty sys (rhs sys)) =>
         Fine2Pretty sys (NamedBinding rhs sys) where
  fine2pretty gamma (NamedBinding maybeName body) opts =
    let gammaExt = gamma ::.. ScSegment maybeName
    in  var2pretty gammaExt VarLast opts |++ " > " |+| fine2pretty gammaExt body opts
instance (SysFinePretty sys,
         Fine2Pretty sys (Mode sys), Fine2Pretty sys (Modality sys), Fine2Pretty sys (rhs sys)) =>
         Show (NamedBinding rhs sys Void) where
  show binding = "[NamedBinding|\n" ++ fine2string @sys ScCtxEmpty binding omit ++ "\n|]"

instance (SysFinePretty sys,
         Fine2Pretty sys (Mode sys), Fine2Pretty sys (Modality sys), Fine2Pretty sys (content sys)) =>
         Fine2Pretty sys (ModalBox content sys) where
  fine2pretty gamma (ModalBox content) opts = fine2pretty gamma content opts

elimination2pretty :: (DeBruijnLevel v,
                       SysFinePretty sys,
                       Fine2Pretty sys (Mode sys), Fine2Pretty sys (Modality sys)) =>
         ScCtx sys v Void ->
         Maybe (ModedModality sys v) ->
         Maybe (Term sys v) ->
         Maybe (UniHSConstructor sys v) ->
         Eliminator sys v ->
         Fine2PrettyOptions sys ->
         PrettyTree String
elimination2pretty gamma maybeDmu maybeEliminee maybeTyEliminee eliminator opts =
  let prettyDmu = maybeDmu & \case
        Just dmu -> fine2pretty gamma dmu opts
        Nothing -> ribbon "_"
      eliminee = fromMaybe (Expr2 TermWildcard) maybeEliminee
      tyEliminee = Type $ fromMaybe (Expr2 TermWildcard) $ hs2term <$> maybeTyEliminee
  in  case eliminator of
        (App arg) ->
          "(" ++| typed2pretty gamma eliminee tyEliminee opts |++ ")" \\\
            [
              " .{" ++| fine2pretty gamma arg opts |++ "}"
            ]
        (Fst) -> "(" ++| typed2pretty gamma eliminee (tyEliminee) opts |++ ") .1 "
        (Snd) -> "(" ++| typed2pretty gamma eliminee (tyEliminee) opts |++ ") ..2 "
        (Unbox) -> "(" ++| typed2pretty gamma eliminee (tyEliminee) opts |++ ") .{}"
        (Funext) -> "funext (" ++| typed2pretty gamma eliminee (tyEliminee) opts |++ ") "
        (ElimDep motive (ElimSigma clausePair)) ->
          ribbon "indSigma " \\\ [
            prettyDmu,
            "(" ++| fine2pretty gamma motive opts |++ ") ",
            "(" ++| fine2pretty gamma clausePair opts |++ ") ",
            "(" ++| typed2pretty gamma eliminee (tyEliminee) opts |++ ") "
          ]
        (ElimDep motive (ElimBox clauseBox)) ->
          ribbon "indBox " \\\ [
            prettyDmu,
            "(" ++| fine2pretty gamma motive opts |++ ") ",
            "(" ++| fine2pretty gamma clauseBox opts |++ ") ",
            "(" ++| typed2pretty gamma eliminee (tyEliminee) opts |++ ") "
          ]
        (ElimDep motive (ElimEmpty)) ->
          ribbon "indEmpty " \\\ [
            prettyDmu,
            "(" ++| fine2pretty gamma motive opts |++ ") ",
            "(" ++| typed2pretty gamma eliminee (tyEliminee) opts |++ ") "
          ]
        (ElimDep motive (ElimNat clauseZero clauseSuc)) ->
          ribbon "indNat " \\\ [
            prettyDmu,
            "(" ++| fine2pretty gamma motive opts |++ ") ",
            "(" ++| fine2pretty gamma clauseZero opts |++ ") ",
            "(" ++| fine2pretty gamma clauseSuc opts |++ ") ",
            "(" ++| typed2pretty gamma eliminee (tyEliminee) opts |++ ") "
          ]
        (ElimEq motive crefl) ->
          ribbon "ind== " \\\ [
            prettyDmu,
            "(" ++| fine2pretty gamma motive opts |++ ") ",
            "(" ++| fine2pretty gamma crefl opts |++ ") ",
            "(" ++| typed2pretty gamma eliminee (tyEliminee) opts |++ ") "
          ]

instance (SysFinePretty sys,
         Fine2Pretty sys (Mode sys), Fine2Pretty sys (Modality sys)) =>
         Fine2Pretty sys (DependentEliminator sys) where
  fine2pretty gamma clauses opts =
    fine2pretty gamma (ElimDep (NamedBinding Nothing $ Type $ Expr2 TermWildcard) clauses) opts
instance (SysFinePretty sys,
         Fine2Pretty sys (Mode sys), Fine2Pretty sys (Modality sys)) =>
         Show (DependentEliminator sys Void) where
  show clauses = "[DependentEliminator|\n" ++ fine2string @sys ScCtxEmpty clauses omit ++ "\n|]"

instance (SysFinePretty sys,
         Fine2Pretty sys (Mode sys), Fine2Pretty sys (Modality sys)) =>
         Fine2Pretty sys (Eliminator sys) where
  fine2pretty gamma elim opts = elimination2pretty gamma Nothing Nothing Nothing elim opts

instance (SysFinePretty sys,
         Fine2Pretty sys (Mode sys), Fine2Pretty sys (Modality sys)) =>
         Show (Eliminator sys Void) where
  show elim = "[Eliminator|\n" ++ fine2string @sys ScCtxEmpty elim omit ++ "\n|]"

instance (SysFinePretty sys,
         Fine2Pretty sys (Mode sys), Fine2Pretty sys (Modality sys)) =>
         Fine2Pretty sys (Algorithm sys) where
  fine2pretty gamma (AlgGoal str (Compose depcies)) opts =
    ribbon ("?" ++ str)
      \\\ ((|++ "}") . (" .{" ++|) . ($ opts) . fine2pretty gamma <$> depcies)
  fine2pretty gamma (AlgSmartElim eliminee (Compose eliminators)) opts =
    "(" ++| fine2pretty gamma eliminee opts |++ ")"
      |+| treeGroup ((" " ++|) . ($ opts) . fine2pretty gamma . snd1 <$> eliminators)
instance (SysFinePretty sys,
         Fine2Pretty sys (Mode sys), Fine2Pretty sys (Modality sys)) =>
         Show (Algorithm sys Void) where
  show alg = "[Algorithm|\n" ++ fine2string @sys ScCtxEmpty alg omit ++ "\n|]"

instance (SysFinePretty sys,
         Fine2Pretty sys (Mode sys), Fine2Pretty sys (Modality sys)) =>
         Fine2Pretty sys (Type sys) where
  fine2pretty gamma (Type t) opts = fine2pretty gamma t opts
deriving instance (SysFinePretty sys,
                   Fine2Pretty sys (Mode sys), Fine2Pretty sys (Modality sys))
    => Show (Type sys Void)

nameWithIndex :: Maybe Raw.Name -> Nat -> PrettyTree String
nameWithIndex maybeName index = (fromMaybe (ribbon "_") $ Raw.unparse' <$> maybeName)
    |++ (toSubscript $ show $ index)

var2pretty :: DeBruijnLevel v => ScCtx sys v Void -> v -> Fine2PrettyOptions sys -> PrettyTree String
var2pretty gamma v opts = nameWithIndex (scGetName gamma v) (getDeBruijnLevel Proxy v)

{-| Term is required to be a meta.
-}
meta2pretty :: (DeBruijnLevel v,
                       SysFinePretty sys,
                       Fine2Pretty sys (Mode sys), Fine2Pretty sys (Modality sys)) =>
  ScCtx sys v Void -> TermNV sys v -> Fine2PrettyOptions sys -> PrettyTree String
meta2pretty gamma tMeta@(TermMeta neutrality meta (Compose depcies) (Compose maybeAlg)) opts =
  ribbon ("?" ++ show meta ++ neutSuffix)
  \\\ case _fine2pretty'printSolutions opts of
        Nothing -> metaNoSolution
        Just solutions -> case lookup meta solutions of
          Nothing -> metaNoSolution
          Just (ForSomeDeBruijnLevel t) ->
            ["\x27ea" ++|
              fine2pretty gamma (join $ (depcies !!) . fromIntegral . getDeBruijnLevel Proxy <$> t) opts
            |++ "\x27eb"]
  where uglySubMeta = (|++ "}") . (" .{" ++|) . ($ opts) . fine2pretty gamma <$> depcies
        metaNoSolution = case maybeAlg of
          Nothing -> uglySubMeta
          Just alg -> if _fine2pretty'humanReadableMetas opts
                      then ["\x27ea" ++| fine2pretty gamma alg opts |++ "\x27eb"]
                      else uglySubMeta
        neutSuffix = case neutrality of
          MetaBlocked -> ""
          MetaNeutral -> "-neutral"
meta2pretty gamma t opts = unreachable

instance (SysFinePretty sys,
         Fine2Pretty sys (Mode sys), Fine2Pretty sys (Modality sys)) =>
         Fine2Pretty sys (TermNV sys) where
  fine2pretty gamma (TermCons consTerm) opts = fine2pretty gamma consTerm opts
  fine2pretty gamma (TermElim mod eliminee tyEliminee eliminator) opts =
    elimination2pretty gamma (Just mod) (Just eliminee) (Just tyEliminee) eliminator opts
  fine2pretty gamma tMeta@(TermMeta neutrality meta (Compose depcies) (Compose maybeAlg)) opts =
    meta2pretty gamma tMeta opts
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
  fine2pretty gamma (TermAlreadyChecked t ty) opts = typed2pretty gamma t ty opts
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
  fine2pretty gamma (TermSys t) opts = fine2pretty gamma t opts
  fine2pretty gamma (TermProblem t) opts = "(! " ++| fine2pretty gamma t opts |++ "!)"
instance (SysFinePretty sys,
         Fine2Pretty sys (Mode sys), Fine2Pretty sys (Modality sys)) =>
         Show (TermNV sys Void) where
  show t = "[TermNV|\n" ++ fine2string @sys ScCtxEmpty t omit ++ "\n|]"

toSubscript :: String -> String
toSubscript = map (\ char -> toEnum $ fromEnum char - 48 + 8320)

instance (SysFinePretty sys,
         Fine2Pretty sys (Mode sys), Fine2Pretty sys (Modality sys), Fine2Pretty sys (termNV sys)) =>
         Fine2Pretty sys (Expr2 termNV sys) where
  fine2pretty gamma (Var2 v) opts = var2pretty gamma v opts
  fine2pretty gamma (Expr2 t) opts = fine2pretty gamma t opts
instance (SysFinePretty sys,
         Fine2Pretty sys (Mode sys), Fine2Pretty sys (Modality sys), Fine2Pretty sys (termNV sys)) =>
         Show (Expr2 termNV sys Void) where
  show e = "[Expr2|\n" ++ fine2string @sys ScCtxEmpty e omit ++ "\n|]"

----------------------

instance (SysFinePretty sys,
         Fine2Pretty sys (Mode sys), Fine2Pretty sys (Modality sys)) =>
         Fine2Pretty sys (Annotation sys) where
  --fine2pretty gamma (AnnotMode d) opts = fine2pretty gamma d opts
  fine2pretty gamma (AnnotModality mu) opts = fine2pretty gamma mu opts
  fine2pretty gamma (AnnotImplicit) opts = ribbon "~"
instance (SysFinePretty sys,
         Fine2Pretty sys (Mode sys), Fine2Pretty sys (Modality sys)) =>
         Show (Annotation sys Void) where
  show annot = "[Annotation|\n" ++ fine2string @sys ScCtxEmpty annot omit ++ "\n|]"

instance (SysFinePretty sys,
         Fine2Pretty sys (Mode sys), Fine2Pretty sys (Modality sys)) =>
         Fine2Pretty sys (Plicity sys) where
  fine2pretty gamma Explicit opts = ribbonEmpty
  fine2pretty gamma Implicit opts = ribbon "~ | "
  fine2pretty gamma (Resolves t) opts = "resolves " ++| fine2pretty gamma t opts |++ " | "
instance (SysFinePretty sys,
         Fine2Pretty sys (Mode sys), Fine2Pretty sys (Modality sys)) =>
         Show (Plicity sys Void) where
  show plic = "[Plicity|\n" ++ fine2string @sys ScCtxEmpty plic omit ++ "\n|]"

declName2pretty :: forall v sys declSort . DeBruijnLevel v =>
  ScCtx sys v Void -> DeclName declSort -> Fine2PrettyOptions sys -> PrettyTree String
declName2pretty gamma (DeclNameVal name) opts = Raw.unparse' name
declName2pretty gamma (DeclNameModule str) opts = ribbon str
declName2pretty gamma (DeclNameSegment maybeName) opts =
  nameWithIndex maybeName (size (Proxy :: Proxy v))
instance Show (DeclName declSort) where
  show declName = "[DeclName|\n" ++ (render (declName2pretty ScCtxEmpty declName $? id) $? id) ++ "\n|]"

{-| Prettyprints a telescope. -}
telescope2pretties :: (DeBruijnLevel v,
         SysFinePretty sys, Functor (ty sys),
         Fine2Pretty sys (Mode sys), Fine2Pretty sys (Modality sys), Fine2Pretty sys (ty sys)) =>
         ScCtx sys v Void -> Telescope ty sys v -> Fine2PrettyOptions sys -> [PrettyTree String]
telescope2pretties gamma (Telescoped Unit2) opts = []
telescope2pretties gamma (seg :|- telescope) opts =
  (fine2pretty gamma seg opts) : telescope2pretties (gamma ::.. (VarFromCtx <$> segment2scSegment seg)) telescope opts
telescope2pretties gamma (mu :** telescope) opts =
  ("{" ++| fine2pretty gamma mu opts |++ "}") : telescope2pretties (() ::\\ gamma) telescope opts
instance (SysFinePretty sys, Functor (ty sys),
         Fine2Pretty sys (Mode sys), Fine2Pretty sys (Modality sys),
         Fine2Pretty sys (ty sys), Fine2Pretty sys (rhs sys)) =>
         Fine2Pretty sys (Telescoped ty rhs sys) where
  fine2pretty gamma telescoped opts =
    (treeGroup $ telescope2pretties gamma (telescoped'telescope telescoped) opts) \\\
    [
      getConst $ mapTelescopedScDB
        (\ wkn gammadelta rhs -> Const $ fine2pretty gammadelta rhs opts)
        gamma telescoped
    ]
instance (SysFinePretty sys, Functor (ty sys),
         Fine2Pretty sys (Mode sys), Fine2Pretty sys (Modality sys), Fine2Pretty sys (ty sys)) =>
         Show (Telescope ty sys Void) where
  show theta = "[Telescope|\n" ++ fine2string @sys ScCtxEmpty theta omit ++ "\n|]"

declAnnots2pretties :: (DeBruijnLevel v,
         SysFinePretty sys,
         Fine2Pretty sys (Mode sys), Fine2Pretty sys (Modality sys)) =>
         ScCtx sys v Void -> Declaration declSort content sys v -> Fine2PrettyOptions sys -> [PrettyTree String]
declAnnots2pretties gamma decl opts = [
                fine2pretty gamma (_decl'modty decl) opts,
                fine2pretty gamma (_decl'plicity decl) opts
              ]

{-
tdeclAnnots2pretties :: (SysFinePretty sys, Functor (ty sys),
         Fine2Pretty sys (Mode sys), Fine2Pretty sys (Modality sys), Fine2Pretty sys ty) =>
         ScCtx sys v Void -> TelescopedDeclaration declSort ty content sys v -> [PrettyTree String]
tdeclAnnots2pretties gamma tdecl =
        getConst (mapTelescopedSc (
            \ wkn gammadelta decl -> Const $ declAnnots2pretties gammadelta decl
          ) gamma tdecl)
-}

seg2pretty ::
  (DeBruijnLevel v,
   SysFinePretty sys, Functor (ty sys),
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
   SysFinePretty sys, Fine2Pretty sys (ty sys)) =>
   Maybe (ModedModality sys v) ->
   ScCtx sys v Void -> Segment ty sys v -> Nat ->
   Fine2PrettyOptions sys -> PrettyTree String
dividedSeg2pretty (Just dmu) gamma seg index opts = dividedSeg2pretty Nothing gamma seg' index opts
  where seg' = over decl'modty (divModedModality dmu) $ seg
dividedSeg2pretty Nothing gamma seg index opts = seg2pretty gamma seg index opts

instance (SysFinePretty sys, Functor (content sys),
         Fine2Pretty sys (Mode sys), Fine2Pretty sys (Modality sys),
         Fine2Pretty sys (content sys)) =>
         Fine2Pretty sys (Declaration declSort content sys) where
  fine2pretty gamma decl opts = case _decl'name decl of
    DeclNameSegment maybeRawName -> seg2pretty gamma decl (size $ _scCtx'sizeProxy gamma) opts
    DeclNameVal rawName ->
      case _fine2pretty'printEntry opts of
        PrintEntryName -> declName2pretty gamma (_decl'name decl) opts
        PrintEntryNameAnnots -> prettyNameAndAnnots
        PrintEntryEntirely -> prettyNameAndAnnots
          ||| fine2pretty gamma (_decl'content decl) opts
      where
        prettyNameAndAnnots = ribbon "val ["
          \\\ declAnnots2pretties gamma decl opts
          /// "] " ++| (declName2pretty gamma (_decl'name decl) opts)
    DeclNameModule str -> case _fine2pretty'printEntry opts of
      PrintEntryName -> declName2pretty gamma (_decl'name decl) opts
      PrintEntryNameAnnots -> prettyNameAndAnnots
      PrintEntryEntirely -> prettyNameAndAnnots
        ||| fine2pretty gamma (_decl'content decl) opts
      where
        prettyNameAndAnnots = ribbon "module  ["
          \\\ declAnnots2pretties gamma decl opts
          /// "] " ++| (declName2pretty gamma (_decl'name decl) opts)
instance (SysFinePretty sys, Functor (content sys),
         Fine2Pretty sys (Mode sys), Fine2Pretty sys (Modality sys),
         Fine2Pretty sys (content sys)) =>
         Show (Declaration declSort content sys Void) where
  show decl = "[Declaration|\n" ++ fine2string @sys ScCtxEmpty decl omit ++ "\n|]"

instance (SysFinePretty sys,
         Fine2Pretty sys (Mode sys), Fine2Pretty sys (Modality sys)) =>
         Fine2Pretty sys (ValRHS sys) where
  fine2pretty gamma (ValRHS tm ty) opts = treeGroup [
      " : " ++| fine2pretty gamma ty opts,
      " = " ++| fine2pretty gamma tm opts
    ]
instance (SysFinePretty sys,
         Fine2Pretty sys (Mode sys), Fine2Pretty sys (Modality sys)) =>
         Show (ValRHS sys Void) where
  show valRHS = "[ValRHS|\n" ++ fine2string @sys ScCtxEmpty valRHS omit ++ "\n|]"

moduleContents2pretty ::
  (SysFinePretty sys, DeBruijnLevel v,
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
        
instance (SysFinePretty sys,
         Fine2Pretty sys (Mode sys), Fine2Pretty sys (Modality sys)) =>
         Fine2Pretty sys (ModuleRHS sys) where
  fine2pretty gamma moduleRHS opts = ribbon " where {"
    \\\ moduleContents2pretty gamma moduleRHS opts
    /// ribbon "}"
instance (SysFinePretty sys,
         Fine2Pretty sys (Mode sys), Fine2Pretty sys (Modality sys)) =>
         Show (ModuleRHS sys Void) where
  show moduleRHS = "[ModuleRHS|\n" ++ fine2string @sys ScCtxEmpty moduleRHS omit ++ "\n|]"

instance (SysFinePretty sys,
         Fine2Pretty sys (Mode sys), Fine2Pretty sys (Modality sys)) =>
         Fine2Pretty sys (Entry sys) where
  fine2pretty gamma (EntryVal val) opts = fine2pretty gamma val opts
  fine2pretty gamma (EntryModule modul) opts = fine2pretty gamma modul opts
instance (SysFinePretty sys,
         Fine2Pretty sys (Mode sys), Fine2Pretty sys (Modality sys)) =>
         Show (Entry sys Void) where
  show entry = "[Entry|\n" ++ fine2string @sys ScCtxEmpty entry omit ++ "\n|]"

twice2pretty gamma ty1 ty2 opts =
    ribbonEmpty \\\ [fine2pretty gamma ty1 opts, ribbon " =[]= ", fine2pretty gamma ty2 opts]

instance (SysFinePretty sys, Functor (ty sys),
         Fine2Pretty sys (Mode sys), Fine2Pretty sys (Modality sys), Fine2Pretty sys (ty sys)) =>
         Fine2Pretty sys (Twice2 ty sys) where
  fine2pretty gamma (Twice2 ty1 ty2) opts = twice2pretty gamma ty1 ty2 opts

--------------------------------------------------

instance Fine2Pretty sys U1 where
  fine2pretty gamma U1 opts = ribbonEmpty

instance Fine2Pretty sys (Unit2 a) where
  fine2pretty gamma Unit2 opts = ribbonEmpty

instance (Fine2Pretty sys f, Fine2Pretty sys g) => Fine2Pretty sys (f :*: g) where
  fine2pretty gamma (a :*: b) opts =
    "(" ++| fine2pretty gamma a opts |++ ", " |+| fine2pretty gamma b opts |++ ")"

instance (Fine2Pretty sys t) => Fine2Pretty sys (Const1 t a) where
  fine2pretty gamma (Const1 t) opts = fine2pretty gamma t opts
