module Menkar.ID where

newtype BlockedConstraintID = BlockedConstraintID {getBlockedConstraintID :: Int}
type MetaID = Int
pattern MetaID meta = (meta :: Int) :: MetaID
getMetaID :: MetaID -> Int
getMetaID meta = meta
