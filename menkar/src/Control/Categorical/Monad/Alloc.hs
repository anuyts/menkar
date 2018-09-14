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

---------------------------------------

newtype AllocT m a s = AllocT {getAllocT :: s -> m (OutAlloc a s)}

instance (Functor m) => C.Functor (AllocT m) (C.NT (->)) (C.NT (->)) where
  fmap (C.NT f) = C.NT $ \ (AllocT comp) -> AllocT $ \ s0 -> (<$> comp s0) $ \case
    OutAlloc s1 a lens -> OutAlloc s1 (f a) lens

instance (Monad m) => C.Monad (AllocT m) (C.NT (->)) where
  return = C.NT $ \ a -> AllocT $ \ s0 -> return $ OutAlloc s0 a id
  bind (C.NT f) = C.NT $ \ (AllocT comp) -> AllocT $ \ s0 -> comp s0 >>= \ case
    OutAlloc s1 a lens1 -> (<$> getAllocT (f a) s1) $ \ case
      OutAlloc s2 b lens2 -> OutAlloc s2 b (lens2 . lens1)

lift1 :: (Functor m) => m (a s) -> AllocT m a s
lift1 ma = AllocT $ \ s0 -> (\ a -> OutAlloc s0 a id) <$> ma

runAllocTWith :: (Functor m) => s -> AllocT m (Const a) s -> m a
runAllocTWith s0 (AllocT comp) = (<$> comp s0) $ \ case
  OutAlloc s1 (Const a) lens -> a

runAllocT :: (Functor m) => AllocT m (Const a) () -> m a
runAllocT = runAllocTWith ()

allocT :: (Applicative m) => a -> AllocT m (AllocRef a) s
allocT a = AllocT $ \ s0 -> pure $ OutAlloc (s0, a) (AllocRef _2) _1

modifyAllT :: (Applicative m) => (s -> s) -> AllocT m U1 s
modifyAllT f = AllocT $ \ s0 -> pure $ OutAlloc (f s0) U1 id
modifyRefT :: (Applicative m) => AllocRef a s -> (a -> a) -> AllocT m U1 s
modifyRefT (AllocRef lens) g = modifyAllT $ over lens $ g

readAllT :: (Applicative m) => AllocT m (Const s) s
readAllT = AllocT $ \ s0 -> pure $ OutAlloc s0 (Const s0) id
readRefT :: (Applicative m) => AllocRef a s -> AllocT m (Const a) s
readRefT (AllocRef lens) = AllocT $ \ s0 -> pure $ OutAlloc s0 (Const $ view lens s0) id

rememberAllT :: (Functor m) => AllocT m a s -> AllocT m (AllocRef s :*: a) s
rememberAllT (AllocT comp) = AllocT $ \ s0 -> (<$> comp s0) $ \ case
  OutAlloc s1 a lens -> OutAlloc s1 (AllocRef lens :*: a) lens

remember1T :: (Functor m) => AllocRef x s -> AllocT m a s -> AllocT m (AllocRef x :*: a) s
remember1T (AllocRef lens0) (AllocT comp) = AllocT $ \ s0 -> (<$> comp s0) $ \ case
  OutAlloc s1 a lens1 -> OutAlloc s1 (AllocRef (lens1 . lens0) :*: a) lens1

-----------------

testT :: [Int]
testT = runAllocT $
  lift1 [Const True, Const False] >>=! \ (Const b) ->
  allocT 5 >>=! \r1 ->
  (remember1T r1 $ return1 $ Const b) >>=! \(r1 :*: y) ->
  (remember1T r1 $ case y of
     Const True ->
       (remember1T r1 $ allocT 7) >>=! \(r1 :*: r2) ->
       (remember1T r1 $ readRefT r2) >>=! \(r1 :*: Const x) ->
       modifyRefT r1 (x +)
     Const False -> return1 U1
  ) >>=! \(r1 :*: U1) ->
  readRefT r1
