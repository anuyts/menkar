module Menkar.ID where

newtype BlockedConstraintID = BlockedConstraintID {getBlockedConstraintID :: Int}
instance Show BlockedConstraintID where
  show (BlockedConstraintID i) = show i

type MetaID = Int
pattern MetaID meta = (meta :: Int) :: MetaID
getMetaID :: MetaID -> Int
getMetaID meta = meta
