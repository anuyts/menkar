module Menkar.Systems.Trivial.Trivial where

import Menkar.Fine.Syntax
import Menkar.System.Scoper
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

import GHC.Generics (U1 (..), V1 (..))
import Data.Void
import Data.Maybe

data Trivial :: KSys where

type instance Mode Trivial = U1
type instance Modality Trivial = U1
type instance Degree Trivial = U1
type instance SysTerm Trivial = V1
type instance SysJudgement Trivial = Void

instance SysTrav Trivial where

instance SysSyntax (Term Trivial) Trivial where
  
instance Fine2Pretty Trivial U1 where
  fine2pretty gamma U1 opts = ribbon "*"
--instance Fine2Pretty Trivial U1 where
--  fine2pretty gamma U1 = ribbon "hoc"
  
instance Multimode Trivial where
  idMod U1 = U1
  compMod U1 U1 U1 = U1
  divMod (ModedModality U1 U1) (ModedModality U1 U1) = U1
  crispMod U1 = U1
  dataMode = U1
  approxLeftAdjointProj (ModedModality U1 U1) U1 = U1
  --term2mode t = U1
  --term2modty t = U1

absurd1 :: V1 x -> a
absurd1 v = undefined

trivModedModality = ModedModality U1 U1

instance Degrees Trivial where
  eqDeg = U1
  maybeTopDeg = Nothing
  divDeg (ModedModality U1 U1) (ModedDegree U1 U1) = U1

instance SysScoper Trivial where
  scopeAnnotation gamma qstring maybeRawArg = scopeFail $ "Illegal annotation: " ++ (render
             (Raw.unparse' qstring \\\ (maybeToList $ Raw.unparse' <$> maybeRawArg))
             $? id
           )

  newMetaMode maybeParent gamma reason = return U1

  newMetaModty maybeParent gamma reason = return U1

instance SysWHN Trivial where
  whnormalizeSys parent gamma t reason = absurd1 t
  leqMod parent gamma U1 U1 U1 U1 reason = return $ Just True
  leqDeg parent gamma U1 U1 U1 reason = return $ Just True
  isEqDeg parent gamma U1 U1 reason = return $ Just True
  isTopDeg parent gamma U1 U1 reason = return $ Just False

instance SysTC Trivial where
  checkTermSys parent gamma t ty = absurd1 t
  newRelatedSysTerm parent deg gammaOrig gamma subst partialInv t ty1 ty2 alternative = absurd1 t
  checkTermRelSysTermWHNTermNoEta parent deg gamma t1 t2 ty1 ty2 = absurd1 t1
  checkEtaWHNSysTy parent gamma t1 t2 = absurd1 t2
  checkMode parent gamma U1 = return ()
  checkModeRel parent gamma U1 U1 = return ()
  checkModality parent gamma U1 U1 U1 = return ()
  checkModalityRel parent modrel gamma U1 U1 U1 U1 = return ()
  checkSysJudgement parent jud = absurd jud

instance Fine2Pretty Trivial V1 where
  fine2pretty gamma t opts = absurd1 t

instance SysPretty Trivial where
  sysJud2pretty jud opts = absurd jud
