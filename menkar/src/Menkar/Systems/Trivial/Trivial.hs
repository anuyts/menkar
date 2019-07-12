module Menkar.Systems.Trivial.Trivial where

import Menkar.Fine.Syntax
import Menkar.Analyzer
import Menkar.System.Scoper
import Menkar.System.Analyzer
import Menkar.System.Fine
import Menkar.System.WHN
import Menkar.System.TC
import Menkar.System.PrettyPrint
import Menkar.PrettyPrint.Fine
import Menkar.Monad
import Menkar.PrettyPrint.Aux.Context
import qualified Menkar.Raw as Raw
import qualified Menkar.PrettyPrint.Raw as Raw

import Text.PrettyPrint.Tree
import Data.Omissible
import Data.Constraint.Witness
import Control.Exception.AssertFalse

import GHC.Generics
import Data.Void
import Data.Maybe
import Data.Functor.Const
import Data.Kind hiding (Type)

data Trivial :: KSys where

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
  analyzableToken = AnTokenMode --AnTokenSys AnTokenMode
  witClassif token = Witness
  analyze token gamma (Classification TrivMode U1 maybeU1) h = Right $ case token of
    TokenTrav -> return $ AnalysisTrav TrivMode
    TokenTC -> return $ AnalysisTC U1
    TokenRel -> return $ AnalysisRel
  convRel token TrivMode = U1
  extraClassif t extraT = U1

instance Analyzable Trivial TrivModality where
  type Classif TrivModality = TrivMode :*: TrivMode
  type Relation TrivModality = Const ModRel
  type ClassifExtraInput TrivModality = U1
  analyzableToken = AnTokenModality --AnTokenSys AnTokenModality
  witClassif token = Witness
  analyze token gamma (Classification TrivModality U1 maybeTrivModes) h = Right $ case token of
    TokenTrav -> return $ AnalysisTrav TrivModality
    TokenTC -> return $ AnalysisTC $ TrivMode :*: TrivMode
    TokenRel -> return $ AnalysisRel
  convRel token TrivMode = U1 :*: U1
  extraClassif t extraT = U1 :*: U1
  
instance Analyzable Trivial TrivDegree where
  type Classif TrivDegree = TrivMode
  type Relation TrivDegree = Const ModRel
  type ClassifExtraInput TrivDegree = U1
  analyzableToken = AnTokenDegree --AnTokenSys AnTokenDegree
  witClassif token = Witness
  analyze token gamma (Classification TrivDegree U1 maybeTrivMode) h = Right $ case token of
    TokenTrav -> return $ AnalysisTrav TrivDegree
    TokenTC -> return $ AnalysisTC $ TrivMode
    TokenRel -> return $ AnalysisRel
  convRel token TrivMode = U1
  extraClassif t extraT = U1

instance Analyzable Trivial TrivTerm where
  type Classif TrivTerm = Type Trivial
  type Relation TrivTerm = ModedDegree Trivial
  type ClassifExtraInput TrivTerm = U1
  analyzableToken = AnTokenSysTerm --AnTokenSys AnTokenTrivTerm
  witClassif token = Witness
  analyze token gamma (Classification syst _ _) h = case syst of {}
  convRel token TrivMode = TrivModedDegree
  extraClassif t extraT = U1
  
instance Analyzable Trivial TrivUniHSConstructor where
  type Classif TrivUniHSConstructor = Classif (UniHSConstructor Trivial)
  type Relation TrivUniHSConstructor = ModedDegree Trivial
  type ClassifExtraInput TrivUniHSConstructor = U1
  analyzableToken = AnTokenSysUniHSConstructor --AnTokenSys AnTokenTrivUniHSConstructor
  witClassif token = Witness
  analyze token gamma (Classification systy _ _) h = case systy of {}
  convRel token TrivMode = U1
  extraClassif t extraT = U1

instance SysTrav Trivial where

instance SysSyntax (Term Trivial) Trivial where

pattern TrivModedModality = ModedModality TrivMode TrivMode TrivModality :: ModedModality Trivial _
pattern TrivModedDegree = ModedDegree TrivMode TrivDegree :: ModedDegree Trivial _

  {-
instance Fine2Pretty Trivial U1 where
  fine2pretty gamma U1 opts = ribbon "*"
--instance Fine2Pretty Trivial U1 where
--  fine2pretty gamma U1 = ribbon "hoc"
-}

instance Multimode Trivial where
  idMod TrivMode = TrivModality
  compMod TrivModality TrivMode TrivModality = TrivModality
  divMod TrivModedModality TrivModedModality = TrivModality
  divMod _ _ = unreachable
  crispMod TrivMode = TrivModality
  dataMode = TrivMode
  approxLeftAdjointProj TrivModedModality = TrivModality
  approxLeftAdjointProj _ = unreachable
  --term2mode t = U1
  --term2modty t = U1

absurd1 :: V1 x -> a
absurd1 v = undefined

trivModedModality = TrivModedModality

instance Degrees Trivial where
  eqDeg d = TrivDegree
  maybeTopDeg d = Nothing
  divDeg TrivModedModality TrivModedDegree = TrivDegree
  divDeg _ _ = unreachable

instance SysScoper Trivial where
  scopeAnnotation gamma qstring maybeRawArg = scopeFail $ "Illegal annotation: " ++ (render
             (Raw.unparse' qstring \\\ (maybeToList $ Raw.unparse' <$> maybeRawArg))
             $? id
           )

  newMetaModeNoCheck gamma reason = return TrivMode

  newMetaModtyNoCheck gamma reason = return TrivModality

  newMetaClassif4sysASTNoCheck token gamma t extraT reason = case token of {}
    {-AnTokenMode -> return $ U1
    AnTokenModality -> return $ TrivMode :*: TrivMode
    AnTokenDegree -> return $ TrivMode
    AnTokenTrivTerm -> case (t :: TrivTerm _) of {}
    AnTokenTrivUniHSConstructor -> case (t :: TrivUniHSConstructor _) of {} -}

instance SysAnalyzer Trivial where
  quickEqSysUnanalyzable sysErr = case sysErr of {}

instance SysWHN Trivial where
  whnormalizeSysTerm gamma t ty reason = case t of {}
  whnormalizeMode gamma TrivMode reason =  return TrivMode
  whnormalizeModality gamma TrivModality TrivMode TrivMode reason = return TrivModality
  whnormalizeDegree gamma TrivDegree TrivMode reason = return TrivDegree
  whnormalizeSys sysToken gamma t extraT classifT reason = case sysToken of {}
  leqMod gamma TrivModality TrivModality TrivMode TrivMode reason = return $ Just True
  leqDeg gamma TrivDegree TrivDegree TrivMode reason = return $ Just True
  isEqDeg gamma TrivDegree TrivMode reason = return $ Just True
  isTopDeg gamma TrivDegree TrivMode reason = return $ Just False

instance SysTC Trivial where
  checkSysASTUnanalyzable sysError = case sysError of {}
  newRelatedSysASTUnanalyzable' sysError = case sysError of {}
  newRelatedSysAST token eta rel gammaOrig gamma subst partialInv t2 extraT1orig extraT2 maybeCTs reason = case token of {}
    {-AnTokenMode -> return TrivMode
    AnTokenModality -> return TrivModality
    AnTokenDegree -> return TrivDegree
    AnTokenTrivTerm -> case (t2 :: TrivTerm _) of {}
    AnTokenTrivUniHSConstructor -> case (t2 :: TrivUniHSConstructor _) of {} -}
  checkUnanalyzableSysASTRel' sysError = case sysError of {}
  checkSysASTRel token eta rel gamma ts extraTs maybeCTs = case token of {}
    {-AnTokenMode -> return ()
    AnTokenModality -> return ()
    AnTokenDegree -> return ()
    AnTokenTrivTerm -> case (fstTwice1 ts :: TrivTerm _) of {}
    AnTokenTrivUniHSConstructor -> case (fstTwice1 ts :: TrivUniHSConstructor _) of {} -}
  checkEtaWHNSysTy gamma t1 syst2 = case syst2 of {}
  etaExpandSysType gamma t sysType = case sysType of {}
  checkSysJudgement jud = case jud of {}

----------------------------------

instance Fine2Pretty Trivial TrivMode where
  fine2pretty gamma TrivMode opts = ribbon "*"

instance Fine2Pretty Trivial TrivModality where
  fine2pretty gamma TrivModality opts = ribbon "*"

instance Fine2Pretty Trivial TrivDegree where
  fine2pretty gamma TrivDegree opts = ribbon "="

instance Fine2Pretty Trivial TrivTerm where
  fine2pretty gamma t opts = case t of {}

instance Fine2Pretty Trivial TrivUniHSConstructor where
  fine2pretty gamma ty opts = case ty of {}

instance SysPretty Trivial where
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
