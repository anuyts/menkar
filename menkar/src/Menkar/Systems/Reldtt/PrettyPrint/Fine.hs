module Menkar.Systems.Reldtt.PrettyPrint.Fine where

import Menkar.Basic
import Menkar.Analyzer
import Menkar.WHN
import Menkar.TC
import Menkar.PrettyPrint
import Menkar.System.Fine
--import Menkar.System.Scoper
--import Menkar.System.WHN
--import Menkar.System.TC
import Menkar.System.PrettyPrint.Fine
import Menkar.Fine
import Menkar.Monad
import Menkar.Systems.Reldtt.Basic
import Menkar.Systems.Reldtt.Fine
import Menkar.Systems.Reldtt.Analyzer
import Menkar.Systems.Reldtt.PrettyPrint.Basic
--import Menkar.Systems.Reldtt.Scoper
--import Menkar.Systems.Reldtt.WHN
--import Menkar.Systems.Reldtt.TC

import Text.PrettyPrint.Tree
import Control.Monad.DoUntilFail
import Control.Exception.AssertFalse
import Data.Functor.Coerce
import Data.Functor.Compose

import Control.Monad
import GHC.Generics
import Data.Functor.Const

instance Fine2Pretty Reldtt ReldttMode where
  fine2pretty gamma (ReldttMode t) opts = fine2pretty gamma t opts

instance Fine2Pretty Reldtt ChainModty where
  fine2pretty gamma chmu opts = case chmu of
    ChainModtyKnown kmu -> fine2pretty gamma kmu opts
    ChainModtyLink knu trho chsigma -> fine2pretty gamma knu opts \\\
        [" \8728(" ++| fine2pretty gamma trho opts |++ ")\8728 "] /+/
      fine2pretty gamma chsigma opts
    ChainModtyTerm dom cod tmu -> "(" ++| fine2pretty gamma tmu opts |++ ")"
    ChainModtyMeta dom cod meta (Compose depcies) -> meta2pretty gamma MetaBlocked meta depcies Nothing opts
    ChainModtyAlreadyChecked dom cod chmuChecked -> fine2pretty gamma chmuChecked opts

instance Fine2Pretty Reldtt ReldttDegree where
  fine2pretty gamma deg opts = case deg of
    DegKnown d kdeg -> ribbon $ knownDeg2string kdeg
    DegGet deg' chmu -> fine2pretty gamma deg' opts \\\
      [" \183(" ++| fine2pretty gamma chmu opts |++ ")"]

instance Fine2Pretty Reldtt KnownModty where
  fine2pretty gamma kmu@(KnownModty snout@(ModtySnout idom icod krevdegs) tail) opts =
    ribbon ("[" ++ (join $ (++ " ") . knownDeg2string <$> reverse krevdegs) ++ prettyTail)
      \\\ typeAnnots
    /// ribbon "]"
    where typeAnnots = if True -- _fine2pretty'printTypeAnnotations opts
            then [ " : " ++| if idom == 0
                             then fine2pretty gamma (_modtyTail'dom tail) opts
                             else "(" ++ show idom ++ " + " ++| fine2pretty gamma (_modtyTail'dom tail) opts |++ ")",
                  " -> " ++| if icod == 0
                             then fine2pretty gamma (_modtyTail'cod tail) opts
                             else "(" ++ show icod ++ " + " ++| fine2pretty gamma (_modtyTail'cod tail) opts |++ ")"]
            else []
          prettyTail = case tail of
            TailEmpty -> ""
            TailDisc _ -> " " ++ maxSnoutPretty ++ " " ++ maxSnoutPretty ++ "\8230"
            TailForget _ -> ""
            TailDiscForget _ _ -> " " ++ maxSnoutPretty ++ " " ++ maxSnoutPretty ++ "\8230"
            TailCont _ -> " " ++ (show idom) ++ " " ++ (show $ idom + 1) ++ " " ++ "\8230"
            TailProblem -> "problem"
          maxSnoutPretty = knownDeg2string $ _snout'max snout

instance Fine2Pretty Reldtt (Const ModtySnout) where
  fine2pretty gamma (Const snout@(ModtySnout idom icod krevdegs)) opts = ribbon $
    (join $ (++ " ") . knownDeg2string <$> reverse krevdegs)
    ++ typeAnnot
    where typeAnnot = if _fine2pretty'printTypeAnnotations opts
            then " : " ++ show idom ++ " -> " ++ show icod
            else ""

instance Fine2Pretty Reldtt ModtyTail where
  fine2pretty gamma tail opts = case tail of
    TailEmpty -> ribbonEmpty
    TailDisc cod -> "{disc " ++| fine2pretty gamma cod opts |++ "}"
    TailForget dom -> "{forget " ++| fine2pretty gamma dom opts |++ "}"
    TailDiscForget dom cod -> fine2pretty gamma (TailDisc dom) opts ||| fine2pretty gamma (TailForget cod) opts
    TailCont d -> "{cont " ++| fine2pretty gamma d opts |++ "}"
    TailProblem -> ribbon "{PROBLEM}"

instance Fine2Pretty Reldtt ReldttSysTerm where
  fine2pretty gamma (SysTermMode modeTerm) opts = fine2pretty gamma modeTerm opts
  fine2pretty gamma (SysTermModty modtyTerm) opts = fine2pretty gamma modtyTerm opts

instance Fine2Pretty Reldtt ReldttUniHSConstructor where
  fine2pretty gamma SysTypeMode opts = ribbon "Mode"
  fine2pretty gamma (SysTypeModty dom cod) opts = ribbon "Modality " \\\ [
    "(" ++| fine2pretty gamma dom opts |++ ") ",
    "(" ++| fine2pretty gamma cod opts |++ ")"]

instance Fine2Pretty Reldtt ModeTerm where
  fine2pretty gamma ModeTermZero opts = ribbon "0"
  fine2pretty gamma (ModeTermSuc t) opts = "suc (" ++| fine2pretty gamma t opts |++ ")"
  fine2pretty gamma ModeTermOmega opts = ribbon "\969"

instance Fine2Pretty Reldtt ModtyTerm where
  fine2pretty gamma modtyTerm opts = case modtyTerm of
    ModtyTermChain chmu -> fine2pretty gamma chmu opts
    ModtyTermDiv tnu tmu -> fine2pretty gamma tnu opts \\\ [" \\ " ++| fine2pretty gamma tmu opts]
    ModtyTermComp tmu2 tmu1 -> fine2pretty gamma tmu2 opts \\\ [" \8728 " ++| fine2pretty gamma tmu1 opts]
    ModtyTermApproxLeftAdjointProj chmu -> "approx-left-adjoint (" ++| fine2pretty gamma chmu opts |++ ")"
    ModtyTermUnavailable dom cod -> ribbon "\8856"

instance SysFinePretty Reldtt where
  sysJud2pretty sysJud opts = case sysJud of {}
  sysToken2string token = case token of
    AnTokenModeTerm -> "mode-term"
    AnTokenModtyTerm -> "modality-term"
    AnTokenKnownModty -> "modality-signature"
    AnTokenModtySnout -> "snout-of-modality-signature"
    AnTokenModtyTail -> "tail-of-modality-signature"
  sysClassif2pretty token gamma extraT ct extraCT opts = case token of
    AnTokenModeTerm -> ribbon "<n/a>"
      where U1 = ct
            U1 = extraT
    AnTokenModtyTerm -> fine2pretty gamma dom opts \\\ [" -> " ++| fine2pretty gamma cod opts]
      where dom :*: cod = ct
            U1 = extraT
    AnTokenKnownModty -> fine2pretty gamma dom opts \\\ [" -> " ++| fine2pretty gamma cod opts]
      where dom :*: cod = ct
            U1 = extraT
    AnTokenModtySnout -> ribbon "<n/a>"
      where U1 = ct
            U1 = extraT
    AnTokenModtyTail -> fine2pretty gamma dom opts \\\ [" -> " ++| fine2pretty gamma cod opts]
      where dom :*: cod = ct
            constSnout = extraT
  sysRelation2pretty token gamma extraT1 extraT2 relT opts = case (token, relT) of
    (AnTokenModeTerm, U1) -> ribbon "="
    (AnTokenModtyTerm, U1) -> ribbon "="
    (AnTokenKnownModty, Const modrel) -> modrel2pretty modrel
    (AnTokenModtySnout, Const modrel) -> modrel2pretty modrel
    (AnTokenModtyTail, Const modrel) -> modrel2pretty modrel
  sysHaveFine2Pretty token a = case token of
    AnTokenModeTerm -> a
    AnTokenModtyTerm -> a
    AnTokenKnownModty -> a
    AnTokenModtySnout -> a
    AnTokenModtyTail -> a
    
