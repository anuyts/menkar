module Menkar.ID where

newtype WorryID = WorryID {getWorryID :: Int}
instance Show WorryID where
  show (WorryID i) = show i

type MetaID = Int
pattern MetaID meta = (meta :: Int) :: MetaID
getMetaID :: MetaID -> Int
getMetaID meta = meta
