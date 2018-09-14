--{-# LANGUAGE TemplateHaskell #-}

module Control.Categorical.Monad.Alloc where

import qualified Control.Category as C
import qualified Control.Categorical.Functor as C
import qualified Control.Categorical.Monad as C
import Control.Categorical.Monad ((>>=!), (>>!), return1)
import Control.Lens
import GHC.Generics

newtype AllocRef a s = AllocRef {allocLens :: Lens' s a}

data OutAlloc a s0 = forall s1 . OutAlloc {
  _alloc'state :: s1,
  _alloc'result :: a s1,
  _alloc'lens :: Lens' s1 s0
  }

newtype Alloc a s = Alloc {getAlloc :: s -> OutAlloc a s}

instance C.Functor Alloc (C.NT (->)) (C.NT (->)) where
  fmap (C.NT f) = C.NT $ \ (Alloc comp) -> Alloc $ \ s0 -> case comp s0 of
    OutAlloc s1 a lens -> OutAlloc s1 (f a) lens

instance C.Monad Alloc (C.NT (->)) where
  return = C.NT $ \ a -> Alloc $ \ s0 -> OutAlloc s0 a id
  bind (C.NT f) = C.NT $ \ (Alloc comp) -> Alloc $ \ s0 -> case comp s0 of
    OutAlloc s1 a lens1 -> case getAlloc (f a) s1 of
      OutAlloc s2 b lens2 -> OutAlloc s2 b (lens2 . lens1)

runAllocWith :: s -> Alloc (Const a) s -> a
runAllocWith s0 (Alloc comp) = case comp s0 of
  OutAlloc s1 (Const a) lens -> a

runAlloc :: Alloc (Const a) () -> a
runAlloc = runAllocWith ()

alloc :: a -> Alloc (AllocRef a) s
alloc a = Alloc $ \ s0 -> OutAlloc (s0, a) (AllocRef _2) _1

modifyAll :: (s -> s) -> Alloc U1 s
modifyAll f = Alloc $ \ s0 -> OutAlloc (f s0) U1 id
modifyRef :: AllocRef a s -> (a -> a) -> Alloc U1 s
modifyRef (AllocRef lens) g = modifyAll $ over lens $ g

readAll :: Alloc (Const s) s
readAll = Alloc $ \ s0 -> OutAlloc s0 (Const s0) id
readRef :: AllocRef a s -> Alloc (Const a) s
readRef (AllocRef lens) = Alloc $ \ s0 -> OutAlloc s0 (Const $ view lens s0) id

rememberAll :: Alloc a s -> Alloc (AllocRef s :*: a) s
rememberAll (Alloc comp) = Alloc $ \ s0 -> case comp s0 of
  OutAlloc s1 a lens -> OutAlloc s1 (AllocRef lens :*: a) lens

remember1 :: AllocRef x s -> Alloc a s -> Alloc (AllocRef x :*: a) s
remember1 (AllocRef lens0) (Alloc comp) = Alloc $ \ s0 -> case comp s0 of
  OutAlloc s1 a lens1 -> OutAlloc s1 (AllocRef (lens1 . lens0) :*: a) lens1

-----------------

test :: Bool -> Int
test b = runAlloc $
  alloc 5 >>=! \r1 ->
  (remember1 r1 $ return1 $ Const b) >>=! \(r1 :*: y) ->
  (remember1 r1 $ case y of
     Const True ->
       (remember1 r1 $ alloc 7) >>=! \(r1 :*: r2) ->
       (remember1 r1 $ readRef r2) >>=! \(r1 :*: Const x) ->
       modifyRef r1 (x +)
     Const False -> return1 U1
  ) >>=! \(r1 :*: U1) ->
  readRef r1
