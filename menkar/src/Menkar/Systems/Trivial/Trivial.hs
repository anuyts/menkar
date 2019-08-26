module Menkar.Systems.Trivial.Trivial where

import Menkar.Fine.Syntax
import Menkar.Analyzer
import Menkar.System
import Menkar.PrettyPrint.Fine
import Menkar.Monad
import Menkar.PrettyPrint.Aux.Context
import qualified Menkar.Raw as Raw
import qualified Menkar.PrettyPrint.Raw as Raw

import Text.PrettyPrint.Tree
import Data.Omissible
import Data.Constraint.Witness
import Control.Exception.AssertFalse
import Data.Functor.Functor1

import GHC.Generics
import Data.Void
import Data.Maybe
import Data.Functor.Const
import Data.Kind hiding (Type)
import Control.Applicative

---------------------------------

data Trivial :: KSys where

---------------------------------

type instance Raw.SysExprC Trivial = Void

---------------------------------

instance SysParser Trivial where
  sysExprC = empty

---------------------------------

instance SysNF Trivial where

---------------------------------

instance SysTrav Trivial where

---------------------------------

instance SysSyntax (Term Trivial) Trivial where

---------------------------------

data TrivMode v = TrivMode
  deriving (Functor, Foldable, Traversable, Generic1, CanSwallow (Term Trivial))
data TrivModality v = TrivModality
  deriving (Functor, Foldable, Traversable, Generic1, CanSwallow (Term Trivial))
data TrivDegree v = TrivDegree
  deriving (Functor, Foldable, Traversable, Generic1, CanSwallow (Term Trivial))
data TrivTerm v where
  deriving (Functor, Foldable, Traversable, Generic1, CanSwallow (Term Trivial))
data TrivUniHSConstructor v where
  deriving (Functor, Foldable, Traversable, Generic1, CanSwallow (Term Trivial))
data TrivJud where
data TrivAnalyzerError where
data TrivAnalyzableToken (t :: * -> *) where
  --AnTokenMode :: TrivAnalyzableToken TrivMode
  --AnTokenModality :: TrivAnalyzableToken TrivModality
  --AnTokenDegree :: TrivAnalyzableToken TrivDegree
  --AnTokenTrivTerm :: TrivAnalyzableToken TrivTerm
  --AnTokenTrivUniHSConstructor :: TrivAnalyzableToken TrivUniHSConstructor

pattern TrivModedModality = TrivModality
pattern TrivModedDegree = TrivDegree
pattern TrivModalityTo = ModalityTo TrivMode TrivModality
--pattern TrivModedModality = ModedModality TrivMode TrivMode TrivModality :: ModedModality Trivial _
--pattern TrivModedDegree = ModedDegree TrivMode TrivDegree :: ModedDegree Trivial _

  {-
instance Fine2Pretty Trivial U1 where
  fine2pretty gamma U1 opts = ribbon "*"
--instance Fine2Pretty Trivial U1 where
--  fine2pretty gamma U1 = ribbon "hoc"
-}

instance Multimode Trivial where
  idMod TrivMode = TrivModality
  compMod TrivModality TrivModality = TrivModality
  divMod TrivModedModality TrivModedModality = TrivModality
  divMod _ _ = unreachable
  crispMod TrivMode = TrivModality
  dataMode = TrivMode
  approxLeftAdjointProj TrivModedModality = TrivModality
  approxLeftAdjointProj _ = unreachable
  _modality'dom TrivModality = TrivMode
  _modality'cod TrivModality = TrivMode
  --term2mode t = U1
  --term2modty t = U1

trivModedModality = TrivModedModality

instance Degrees Trivial where
  eqDeg d = TrivDegree
  maybeTopDeg d = Nothing
  divDeg TrivModedModality TrivModedDegree = TrivDegree
  divDeg _ _ = unreachable
  _degree'mode TrivDegree = TrivMode

---------------------------------

type instance Mode Trivial = TrivMode
type instance Modality Trivial = TrivModality
type instance Degree Trivial = TrivDegree
type instance SysTerm Trivial = TrivTerm
type instance SysUniHSConstructor Trivial = TrivUniHSConstructor
type instance SysJudgement Trivial = TrivJud
type instance SysAnalyzerError Trivial = TrivAnalyzerError

type instance SysAnalyzableToken Trivial = TrivAnalyzableToken

instance Analyzable Trivial TrivMode where
  type Classif TrivMode = U1
  type Relation TrivMode = U1
  type ClassifExtraInput TrivMode = U1
  analyzableToken = AnTokenMultimode AnTokenMode --AnTokenSys AnTokenMode
  witClassif token = Witness
  analyze token gamma (Classification TrivMode U1 maybeU1) h = Right $ case token of
    TokenTrav -> return $ AnalysisTrav TrivMode
    TokenTC -> return $ AnalysisTC U1
    TokenRel -> return $ AnalysisRel
  convRel token d = U1
  extraClassif d t extraT = U1

instance Analyzable Trivial TrivModality where
  type Classif TrivModality = TrivMode :*: TrivMode
  type Relation TrivModality = Const ModRel
  type ClassifExtraInput TrivModality = U1
  analyzableToken = AnTokenMultimode AnTokenModality --AnTokenSys AnTokenModality
  witClassif token = Witness
  analyze token gamma (Classification TrivModality U1 maybeTrivModes) h = Right $ case token of
    TokenTrav -> return $ AnalysisTrav TrivModality
    TokenTC -> return $ AnalysisTC $ TrivMode :*: TrivMode
    TokenRel -> return $ AnalysisRel
  convRel token d = U1 :*: U1
  extraClassif d t extraT = U1 :*: U1
  
instance Analyzable Trivial TrivDegree where
  type Classif TrivDegree = TrivMode
  type Relation TrivDegree = Const ModRel
  type ClassifExtraInput TrivDegree = U1
  analyzableToken = AnTokenMultimode AnTokenDegree --AnTokenSys AnTokenDegree
  witClassif token = Witness
  analyze token gamma (Classification TrivDegree U1 maybeTrivMode) h = Right $ case token of
    TokenTrav -> return $ AnalysisTrav TrivDegree
    TokenTC -> return $ AnalysisTC $ TrivMode
    TokenRel -> return $ AnalysisRel
  convRel token d = U1
  extraClassif d t extraT = U1

instance Analyzable Trivial TrivTerm where
  type Classif TrivTerm = Type Trivial
  type Relation TrivTerm = ModedDegree Trivial
  type ClassifExtraInput TrivTerm = U1
  analyzableToken = AnTokenSysTerm --AnTokenSys AnTokenTrivTerm
  witClassif token = Witness
  analyze token gamma (Classification syst _ _) h = case syst of {}
  convRel token d = TrivModedDegree
  extraClassif d t extraT = U1
  
instance Analyzable Trivial TrivUniHSConstructor where
  type Classif TrivUniHSConstructor = Classif (UniHSConstructor Trivial)
  type Relation TrivUniHSConstructor = ModedDegree Trivial
  type ClassifExtraInput TrivUniHSConstructor = U1
  analyzableToken = AnTokenSysUniHSConstructor --AnTokenSys AnTokenTrivUniHSConstructor
  witClassif token = Witness
  analyze token gamma (Classification systy _ _) h = case systy of {}
  convRel token d = U1
  extraClassif d t extraT = TrivModalityTo :*: U1

instance SysAnalyzer Trivial where
  quickEqSysUnanalyzable sysErr = case sysErr of {}

---------------------------------

instance SysScoper Trivial where
  rawRootAnnots = []
  
  scopeAnnotation gamma string maybeRawArg = scopeFail $ "Illegal annotation: " ++ (render
             (ribbon string \\\ (maybeToList $ Raw.unparse' <$> maybeRawArg))
             $? id
           )

  scopeSysExprC gamma sysExprC = absurd sysExprC

  newMetaModeNoCheck gamma reason = return TrivMode

  newMetaModtyNoCheck gamma reason = return TrivModality

  newMetaClassif4sysASTNoCheck token gamma t extraT reason = case token of {}
    {-AnTokenMode -> return $ U1
    AnTokenModality -> return $ TrivMode :*: TrivMode
    AnTokenDegree -> return $ TrivMode
    AnTokenTrivTerm -> case (t :: TrivTerm _) of {}
    AnTokenTrivUniHSConstructor -> case (t :: TrivUniHSConstructor _) of {} -}

---------------------------------

instance SysWHN Trivial where
  whnormalizeSysTerm gamma t ty reason = case t of {}
  --whnormalizeMode gamma TrivMode reason =  return TrivMode
  --whnormalizeModality gamma TrivModality TrivMode TrivMode reason = return TrivModality
  --whnormalizeDegree gamma TrivDegree TrivMode reason = return TrivDegree
  whnormalizeMultimodeOrSysAST token gamma t extraT classifT reason = case token of
    Left AnTokenMode -> return TrivMode
    Left AnTokenModality -> return TrivModality
    Left AnTokenDegree -> return TrivDegree
    Right sysToken -> case sysToken of {}
  leqMod gamma TrivModality TrivModality TrivMode TrivMode reason = return $ Just True
  leqDeg gamma TrivDegree TrivDegree TrivMode reason = return $ Just True
  isEqDeg gamma TrivDegree TrivMode reason = return $ Just True
  isTopDeg gamma TrivDegree TrivMode reason = return $ Just False

---------------------------------

instance SysTC Trivial where
  checkSysASTUnanalyzable sysError = case sysError of {}
  newRelatedSysASTUnanalyzable' sysError = case sysError of {}
  newRelatedMultimodeOrSysAST token eta rel gammaOrig gamma subst partialInv t2 extraT1orig extraT2 maybeCTs reason =
    case token of
      Left AnTokenMode -> return TrivMode
      Left AnTokenModality -> return TrivModality
      Left AnTokenDegree -> return TrivDegree
      Right sysToken -> case sysToken of {}
      --Left AnTokenTrivTerm -> case (t2 :: TrivTerm _) of {}
      --Left AnTokenTrivUniHSConstructor -> case (t2 :: TrivUniHSConstructor _) of {}
  checkUnanalyzableSysASTRel' sysError = case sysError of {}
  checkMultimodeOrSysASTRel token eta rel gamma ts extraTs maybeCTs = case token of
    Left AnTokenMode -> return ()
    Left AnTokenModality -> return ()
    Left AnTokenDegree -> return ()
    Right sysToken -> case sysToken of {}
    --AnTokenTrivTerm -> case (fstTwice1 ts :: TrivTerm _) of {}
    --AnTokenTrivUniHSConstructor -> case (fstTwice1 ts :: TrivUniHSConstructor _) of {}
  -- checkEtaWHNSysTy gamma t1 syst2 = case syst2 of {}
  checkEtaMultimodeOrSys token gamma t extraT ct = unreachable -- there are no solvable system-specific ASTs.
  etaExpandSysType useHoles gamma t sysType = case sysType of {}
  checkSysJudgement jud = case jud of {}

----------------------------------

instance Raw.Unparsable Void where
  unparse' = absurd
  parserName _ = "empty"

instance Raw.SysRawPretty Trivial where

----------------------------------

instance Fine2Pretty Trivial TrivMode where
  fine2pretty gamma TrivMode opts = ribbon "_"

instance Fine2Pretty Trivial TrivModality where
  fine2pretty gamma TrivModality opts = ribbon "_"

instance Fine2Pretty Trivial TrivDegree where
  fine2pretty gamma TrivDegree opts = ribbon "="

instance Fine2Pretty Trivial TrivTerm where
  fine2pretty gamma t opts = case t of {}

instance Fine2Pretty Trivial TrivUniHSConstructor where
  fine2pretty gamma ty opts = case ty of {}

instance SysFinePretty Trivial where
  sysJud2pretty jud opts = case jud of {}
  sysToken2string token = case token of {}
    {-AnTokenMode -> "mode"
    AnTokenModality -> "modality"
    AnTokenDegree -> "degree"
    AnTokenTrivTerm -> "system-specific-term_(impossible)"
    AnTokenTrivUniHSConstructor -> "system-specific-UniHS-constructor_(impossible)"-}
  sysClassif2pretty token gamma extraT ct extraCT opts = case token of {}
    {-AnTokenMode -> ribbon "mode"
    AnTokenModality -> ribbon "modality"
    AnTokenDegree -> ribbon "degree"
    AnTokenTrivTerm -> fine2pretty gamma ct opts
    AnTokenTrivUniHSConstructor -> fine2pretty gamma ct opts-}
  sysRelation2pretty token gamma extraT1 extraT2 rel opts = case token of {}
    {-AnTokenMode -> ribbon "="
    AnTokenModality -> modrel2pretty $ getConst rel
    AnTokenDegree -> modrel2pretty $ getConst rel
    AnTokenTrivTerm -> "[" ++| fine2pretty gamma rel opts |++ "]"
    AnTokenTrivUniHSConstructor -> "[" ++| fine2pretty gamma rel opts |++ "]"-}
  sysHaveFine2Pretty token a = case token of {}
    {-AnTokenMode -> a
    AnTokenModality -> a
    AnTokenDegree -> a
    AnTokenTrivTerm -> a
    AnTokenTrivUniHSConstructor -> a-}
