module Menkar.Basic.Syntax where

import GHC.Generics
import Data.Hashable
import Data.Number.Nat

data Opness = NonOp | Op deriving (Show, Eq, Generic, Hashable)

data Name = Name {opnessName :: Opness, stringName :: String} deriving (Eq, Generic, Hashable) --deriving Show

data Qualified a = Qualified [String] a deriving (Functor, Foldable, Traversable, Eq)
--deriving instance Show a => Show (Qualified a)

type QName = Qualified Name

data ArgSpec = ArgSpecNext | ArgSpecExplicit | ArgSpecNamed String deriving Show

data ProjSpec = ProjSpecNamed String | ProjSpecNumbered Nat | ProjSpecTail Nat deriving Show
