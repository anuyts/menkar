module Menkar.ID where

import Control.DeepSeq.Redone

import GHC.Generics

newtype WorryID = WorryID {getWorryID :: Int}
  deriving newtype NFData
instance Show WorryID where
  show (WorryID i) = show i

type MetaID = Int
pattern MetaID meta = (meta :: Int) :: MetaID
getMetaID :: MetaID -> Int
getMetaID meta = meta
