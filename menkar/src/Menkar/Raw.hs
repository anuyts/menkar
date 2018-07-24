module Menkar.Raw where

data Module = Module [Entry] deriving (Show)
data Pseudo = Pseudo deriving (Show)
data File = File [Pseudo] Module deriving (Show)
data Entry = ModuleEntry Module | PseudoEntry Pseudo deriving (Show)
data Annotation = Annotation
