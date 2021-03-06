module Menkar.Basic.Syntax where

import Control.DeepSeq.Redone

import GHC.Generics
import Data.Hashable

data Opness = NonOp | Op deriving (Show, Eq, Generic, Hashable, NFData)

data Name = Name {opnessName :: Opness, stringName :: String} deriving (Eq, Generic, Hashable, NFData) --deriving Show

data Qualified a = Qualified [String] a deriving (Functor, Foldable, Traversable, Eq, Generic1, NFData1)
--deriving instance Show a => Show (Qualified a)

type QName = Qualified Name

data ArgSpec = ArgSpecNext | ArgSpecExplicit | ArgSpecNamed Name deriving (Generic, NFData)

data ProjSpec = ProjSpecNamed Name | ProjSpecNumbered Int | ProjSpecTail Int deriving (Generic, NFData)

