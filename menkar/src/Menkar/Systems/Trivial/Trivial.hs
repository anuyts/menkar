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

type instance Mode Trivial = TrivMode
type instance Modality Trivial = TrivModality
type instance Degree Trivial = TrivDegree
type instance SysTerm Trivial = TrivTerm
type instance SysUniHSConstructor Trivial = TrivUniHSConstructor
type instance SysJudgement Trivial = TrivJud
type instance SysAnalyzerError Trivial = TrivAnalyzerError

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
  quickEqSysUnanalyzable sysErr _ _ _ _ = case sysErr of {}

instance SysWHN Trivial where
  whnormalizeSys parent gamma t reason = case t of {}
  leqMod parent gamma TrivModality TrivModality TrivMode TrivMode reason = return $ Just True
  leqDeg parent gamma TrivDegree TrivDegree TrivMode reason = return $ Just True
  isEqDeg parent gamma TrivDegree TrivMode reason = return $ Just True
  isTopDeg parent gamma TrivDegree TrivMode reason = return $ Just False

instance SysTC Trivial where
  checkTermSys parent gamma t ty = absurd1 t
  --newRelatedSysTerm parent deg gammaOrig gamma subst partialInv t ty1 ty2 alternative = absurd1 t
  --checkTermRelSysTermWHNTermNoEta parent deg gamma t1 t2 ty1 ty2 = absurd1 t1
  checkEtaWHNSysTy parent gamma t1 t2 = absurd1 t2
  checkSysUniHSConstructor parent gamma t ty = absurd1 t
  newRelatedSysUniHSConstructor parent deg gammaOrig gamma subst partialInv t = absurd1 t
  etaExpandSysType parent gamma t sysType = absurd1 sysType
  checkSysUniHSConstructorRel parent deg gamma t1 t2 ty1 ty2 metasTy1 metasTy2 = absurd1 t1
  checkMode parent gamma U1 = return ()
  checkModeRel parent gamma U1 U1 = return ()
  checkModality parent gamma U1 U1 U1 = return ()
  checkModalityRel parent modrel gamma U1 U1 U1 U1 = return ()
  checkSysJudgement parent jud = absurd jud

instance Fine2Pretty Trivial V1 where
  fine2pretty gamma t opts = absurd1 t

instance SysPretty Trivial where
  sysJud2pretty jud opts = absurd jud
