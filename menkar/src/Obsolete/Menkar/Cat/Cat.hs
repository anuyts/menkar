{-# LANGUAGE TypeFamilies, PolyKinds, ConstraintKinds, KindSignatures, FlexibleInstances, RankNTypes,
MultiParamTypeClasses, GADTs, FunctionalDependencies, PartialTypeSignatures, TypeApplications #-}

module Menkar.Cat.Cat where

import GHC.Exts (Constraint)

-- THIS REALLY DOESN'T WORK

--------------------------

data Witness (c :: Constraint) where
  Witness :: c => Witness c

trust :: Witness c -> (c => d) -> d
trust Witness d = d

--------------------------

class Cat (obj :: k -> Constraint) (hom :: k -> k -> *) | hom -> obj, obj -> hom where
  idhom :: obj x => hom x x
  (%) :: (obj x, obj y, obj z) => hom y z -> hom x y -> hom x z
infixr 9 %

class (Cat objA homA, Cat objB homB) => HFunctor objA homA objB homB f |
  f -> objA, f -> homA, f -> objB, f -> homB, objA -> homA, homA -> objA, objB -> homB, homB -> objB where
  fobj :: Witness (objA x) -> Witness (objB (f x))
  fhom :: (objA x, objA y) => homA x y -> homB (f x) (f y)

--------------------------

class Any x where

instance Any x where

--------------------------

instance Cat Any (->) where
  idhom = id
  (%) = (.)

--------------------------

newtype NT (objA :: ka -> Constraint) (homA :: ka -> ka -> *)
           (objB :: kb -> Constraint) (homB :: kb -> kb -> *)
           (f :: ka -> kb) (g :: ka -> kb)
  = NT {runNT :: (forall a .(Cat objA homA, Cat objB homB, objA a) => homB (f a) (g a))}

instance (Cat objA homA, Cat objB homB) => Cat (HFunctor objA homA objB homB) (NT objA homA objB homB) where
  idhom = NT (trust _ idhom)
  --idhom = NT (trust (fobj (Witness :: Witness (objA _)) :: Witness (objB _)) idhom)
  NT nu % NT mu = _ --NT (trust _ $ nu % mu)

{-

class HomSet (hom :: k -> k -> *) where
  type Obj hom :: k -> Constraint
  idhom :: Obj hom x => hom x x
  (%) :: (Obj hom x, Obj hom y, Obj hom z) => hom y z -> hom x y -> hom x z

class Any x where

instance Any x where

{-| Instances should have the property that @ Obj dom x => Obj cod (f x) @.
-}
class (HomSet dom, HomSet cod) => HFunctor dom cod f where
  fobj :: Obj dom x => Witness (Obj cod (f x))
  fhom :: (Obj dom x, Obj dom y) => dom x y -> cod (f x) (f y)

--------------------------

instance HomSet (->) where
  type Obj (->) = Any
  idhom = id
  (%) = (.)
infixr 9 %

--------------------------

{-| Natural transformations from 'f' to 'g' with domain 'dom' and codomain 'cod'
-}
newtype NT (dom :: kdom -> kdom -> *)
           (cod :: kcod -> kcod -> *)
           (f :: kdom -> kcod) (g :: kdom -> kcod)
  = NT {runNT :: (forall a. (Obj dom a) => cod (f a) (g a))}

instance (HomSet dom, HomSet cod) => HomSet (NT dom cod) where
  type Obj (NT dom cod) = HFunctor dom cod
  idhom = NT idhom
  NT nu % NT mu = NT (nu % mu)
-}
