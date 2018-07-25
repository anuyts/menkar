module Menkar.Raw where

data LHS = LHS {annotations :: [Annotation], name :: String} deriving (Show)
data RHS = RHSModule [Entry] deriving (Show)
--data Module = Module [Entry] deriving (Show)
data PseudoEntry = PseudoEntry deriving (Show)
data GenuineEntry = GenuineEntry LHS RHS deriving (Show)
data File = File [PseudoEntry] GenuineEntry deriving (Show)
data Entry = EntryGenuine GenuineEntry | EntryPseudo PseudoEntry deriving (Show)
data Annotation = AnnotationAtomic String | AnnotationHaskell String deriving (Show)
