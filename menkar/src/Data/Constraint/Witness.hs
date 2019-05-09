module Data.Constraint.Witness where

data Witness a = a => Witness

have :: Witness a -> (a => b) -> b
have Witness b = b
