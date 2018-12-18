module Control.Monad.MCont where

import Control.Monad.Trans.Class

data MContT r m a = MContT {
  runMContT :: (m a -> m r) -> m r
  } deriving Functor

evalMContT :: MContT r m r -> m r
evalMContT cmr = cmr `runMContT` id

instance (Applicative m) => Applicative (MContT r m) where
  pure a = MContT $ \ kma -> kma $ pure a
  cmf <*> cma = MContT $ \ kmb ->
    let appk mf ma = kmb $ mf <*> ma
        kma ma = cmf `runMContT` (flip appk ma)
    in  cma `runMContT` kma

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

{-
instance Monad m => MonadDC r (ContT r m) where
  shiftDC f = ContT $ \ k -> f (lift . k) `runContT` return
  resetDC = lift . evalContT
-}
