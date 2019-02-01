module Menkar.Fine.System.System where

class (Functor (Mode sys), Functor (Modality sys), Functor (Degree sys)) => System sys where
  type Mode sys :: * -> *
  type Modality sys :: * -> *
  type Degree sys :: * -> *
