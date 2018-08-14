{-# LANGUAGE MultiParamTypeClasses, PolyKinds, DataKinds, TypeFamilies, RankNTypes, ConstraintKinds, GADTs,
FlexibleInstances #-}
data OpLambdaApp fs where
  App :: OpLambdaApp [Identity, Identity]

--TODO: use 'Either (r :: *) v' instead of '(f :: Traversable) v'
