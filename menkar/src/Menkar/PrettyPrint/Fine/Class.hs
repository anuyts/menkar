{-# LANGUAGE UndecidableInstances #-}

module Menkar.PrettyPrint.Fine.Class where

import Menkar.System.Fine
import Menkar.Fine.Syntax
import Menkar.Basic.Context
import Menkar.PrettyPrint.Aux.Context

import Text.PrettyPrint.Tree
import Data.Omissible

import Data.IntMap.Lazy hiding (map, size)
import Control.Lens
import Data.Void

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

class Fine2Pretty sys t where
  fine2pretty :: forall v . DeBruijnLevel v => ScCtx sys v Void -> t v -> Fine2PrettyOptions sys -> PrettyTree String
  fine2string :: forall v . DeBruijnLevel v => ScCtx sys v Void -> t v -> Fine2PrettyOptions sys -> String
  fine2string gamma x opts = render (fine2pretty gamma x opts) $ _fine2pretty'renderOptions opts

instance Fine2Pretty sys t => Fine2Pretty sys (Box1 t) where
  fine2pretty gamma (Box1 t) opts = fine2pretty gamma t opts
