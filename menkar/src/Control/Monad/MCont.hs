{-# LANGUAGE UndecidableInstances #-}

module Control.Monad.MCont where

import Control.Monad.Trans.Class
import Control.Monad.State
import Control.Monad.Except

data MContT r m a = MContT {
  runMContT :: (m a -> m r) -> m r
  } deriving Functor

evalMContT :: MContT r m r -> m r
evalMContT cmr = cmr `runMContT` id

instance (Monad m) => Applicative (MContT r m) where
  pure a = MContT $ \ kma -> kma $ pure a
  cmf <*> cma = cmf >>= \ f -> f <$> cma
  {-
  (cmg :: MContT r m (t -> b)) <*> (cmt :: MContT r m t) =
    MContT $ \ kmb ->
      let f :: (t -> b) -> MContT r m b
          f g' = g' <$> cmt
          kg :: (t -> b) -> m r b
          kg = \ g' -> f g' `runMContT` kmb
      in  cmg `runMContT` (>>= kg)
-}

    {-MContT $ \ kmb ->
    let appk mf ma = kmb $ mf <*> ma
        kma ma = cmf `runMContT` (flip appk ma)
    in  cma `runMContT` kma-}

instance (Monad m) => Monad (MContT r m) where
  cma >>= f = MContT $ \ kmb ->
    let ka = \ a -> f a `runMContT` kmb
    in  cma `runMContT` (>>= ka)

instance MonadTrans (MContT r) where
  lift ma = MContT $ \ kma -> kma ma

-- | delimited continuation monad class
class Monad m => MonadDC r m | m -> r where
  shiftDC :: ((a -> m r) -> m r) -> m a
  resetDC :: m r -> m r
class MonadDC r m => MonadMDC r m | m -> r where
  shiftMDC :: ((m a -> m r) -> m r) -> m a
  resetMDC :: m r -> m r
  resetMDC = resetDC

mapMContT :: (m a -> m b) -> MContT r m a -> MContT r m b
mapMContT f cma = MContT $ \kmb -> cma `runMContT` (kmb . f)

instance Monad m => MonadDC r (MContT r m) where
  shiftDC f = MContT $ \ kma -> evalMContT $ f (lift . kma . return)
  resetDC = lift . evalMContT
instance Monad m => MonadMDC r (MContT r m) where
  shiftMDC f = MContT $ \ kma -> evalMContT $ f (mapMContT kma)

instance MonadState s m => MonadState s (MContT r m) where
  get = lift get
  put = lift . put
  state = lift . state

instance (MonadError e m) => MonadError e (MContT r m) where
  throwError e = lift $ throwError e
  -- CAREFUL: this also catches errors thrown in the future, i.e. by the continuation!!!
  catchError cma handle = MContT $ \kma -> catchError (runMContT cma kma) (\e -> runMContT (handle e) kma)

{-
instance Monad m => MonadDC r (ContT r m) where
  shiftDC f = ContT $ \ k -> f (lift . k) `runContT` return
  resetDC = lift . evalContT
-}
