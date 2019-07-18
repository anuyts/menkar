module Menkar.Systems.Reldtt.Basic where

import Menkar.System.Basic

data Reldtt :: KSys where

data KnownDeg =
  KnownDegEq |
  KnownDeg Int |
  KnownDegOmega {-^ Only allowed in infinite modes. -} |
  KnownDegTop |
  KnownDegProblem
  deriving (Eq, Ord)

-- | It is an error to create a @'ModtySnout'@ whose length differs from its codomain.
data ModtySnout = ModtySnout
  {_modtySnout'dom :: Int,
   _modtySnout'cod :: Int,
   {-| Degrees in REVERSE ORDER. -}
   _modtySnout'degreesReversed :: [KnownDeg]
  } deriving Eq
instance Ord ModtySnout where
  ModtySnout idom1 icod1 krevdegs1 <= ModtySnout idom2 icod2 krevdegs2 =
    idom1 == idom2 && icod1 == icod2 && all (\ (i1, i2) -> i1 <= i2) (zip krevdegs1 krevdegs2)
