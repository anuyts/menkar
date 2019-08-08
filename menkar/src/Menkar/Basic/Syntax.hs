module Menkar.Basic.Syntax where

import GHC.Generics
import Data.Hashable

data Opness = NonOp | Op deriving (Show, Eq, Generic, Hashable)

data Name = Name {opnessName :: Opness, stringName :: String} deriving (Eq, Generic, Hashable) --deriving Show

data Qualified a = Qualified [String] a deriving (Functor, Foldable, Traversable, Eq)
--deriving instance Show a => Show (Qualified a)

type QName = Qualified Name

data ArgSpec = ArgSpecNext | ArgSpecExplicit | ArgSpecNamed Name --deriving Show

data ProjSpec = ProjSpecNamed Name | ProjSpecNumbered Int | ProjSpecTail Int --deriving Show

