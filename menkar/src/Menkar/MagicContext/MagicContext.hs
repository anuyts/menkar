module Menkar.MagicContext.MagicContext where

import Menkar.Fine
import Menkar.System.Basic
import Menkar.System.Fine
import Menkar.Analyzer
import Menkar.System.MagicContext

import Data.Void
import GHC.Generics

magicContext :: forall sys . (Multimode sys, SysMagicContext sys) => Ctx Type sys (VarInModule Void) Void
magicContext = CtxEmpty dataMode :<...> absurd <$> magicModule

magicModuleCorrect :: forall sys . (SysAnalyzer sys, SysMagicContext sys) => Judgement sys
magicModuleCorrect =
  (Jud
    (AnTokenDeclaration $ AnTokenTelescoped $ AnTokenModuleRHS)
    (CtxEmpty dataMode)
    (Declaration
      (DeclNameModule "magic")
      (idModalityTo dataMode)
      Explicit
      (Telescoped $ magicModule)
    )
    U1
    (ClassifWillBe U1)
  )
