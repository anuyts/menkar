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
data TrivTerm v
  deriving (Functor, Foldable, Traversable, Generic1, CanSwallow (Term Trivial))
data TrivUniHSConstructor v
  deriving (Functor, Foldable, Traversable, Generic1, CanSwallow (Term Trivial))
data TrivJud
data TrivAnalyzerError
data TrivAnalyzableToken (t :: * -> *)

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

instance Analyzable Trivial TrivModality where
  type Classif TrivModality = TrivMode :*: TrivMode
  type Relation TrivModality = Const ModRel
  type ClassifExtraInput TrivModality = U1
  
instance Analyzable Trivial TrivDegree where
  type Classif TrivDegree = TrivMode
  type Relation TrivDegree = Const ModRel
  type ClassifExtraInput TrivDegree = U1

instance Analyzable Trivial TrivTerm where
  type Classif TrivTerm = Type Trivial
  type Relation TrivTerm = ModedDegree Trivial
  type ClassifExtraInput TrivTerm = U1
  
instance Analyzable Trivial TrivUniHSConstructor where
  type Classif TrivUniHSConstructor = Classif (UniHSConstructor Trivial)
  type Relation TrivUniHSConstructor = ModedDegree Trivial
  type ClassifExtraInput TrivUniHSConstructor = U1

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
  crispMod TrivMode = TrivModality
  dataMode = TrivMode
  approxLeftAdjointProj TrivModedModality = TrivModality
  --term2mode t = U1
  --term2modty t = U1

absurd1 :: V1 x -> a
absurd1 v = undefined

trivModedModality = TrivModedModality

instance Degrees Trivial where
  eqDeg = TrivDegree
  maybeTopDeg = Nothing
  divDeg TrivModedModality TrivModedDegree = TrivDegree

instance SysScoper Trivial where
  scopeAnnotation gamma qstring maybeRawArg = scopeFail $ "Illegal annotation: " ++ (render
             (Raw.unparse' qstring \\\ (maybeToList $ Raw.unparse' <$> maybeRawArg))
             $? id
           )

  newMetaModeNoCheck maybeParent gamma reason = return TrivMode

  newMetaModtyNoCheck maybeParent gamma reason = return TrivModality

instance SysAnalyzer Trivial where
  quickEqSysUnanalyzable sysErr = case sysErr of {}

instance SysWHN Trivial where
  whnormalizeSys parent gamma t reason = case t of {}
  leqMod parent gamma TrivModality TrivModality TrivMode TrivMode reason = return $ Just True
  leqDeg parent gamma TrivDegree TrivDegree TrivMode reason = return $ Just True
  isEqDeg parent gamma TrivDegree TrivMode reason = return $ Just True
  isTopDeg parent gamma TrivDegree TrivMode reason = return $ Just False

instance SysTC Trivial where
  checkSysASTUnanalyzable sysError = case sysError of {}
  newRelatedSysASTUnanalyzable' sysError = case sysError of {}
  newRelatedSysAST token = case token of {}
  checkUnanalyzableSysASTRel' sysError = case sysError of {}
  checkSysASTRel token = case token of {}
  checkEtaWHNSysTy parent gamma t1 syst2 = case syst2 of {}
  etaExpandSysType parent gamma t sysType = case sysType of {}
  checkSysJudgement parent jud = case jud of {}

instance SysPretty Trivial where
  sysJud2pretty jud opts = case jud of {}
