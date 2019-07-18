module Menkar.Systems.Reldtt.PrettyPrint.Basic where

import Menkar.Basic
import Menkar.Systems.Reldtt.Basic

import Text.PrettyPrint.Tree

import Control.Monad

knownDeg2string :: KnownDeg -> String
knownDeg2string KnownDegEq = "="
knownDeg2string (KnownDeg i) = show i
knownDeg2string KnownDegOmega = "\969"
knownDeg2string KnownDegTop = "T"
knownDeg2string KnownDegProblem = "!"

snout2string :: ModtySnout -> String
snout2string snout@(ModtySnout idom icod krevdegs) =
    (join $ (++ " ") . knownDeg2string <$> reverse krevdegs)
    ++ " : " ++ show idom ++ " -> " ++ show icod
