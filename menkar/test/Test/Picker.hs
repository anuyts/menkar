{-# LANGUAGE GADTs, DeriveFunctor, StandaloneDeriving, RankNTypes, ApplicativeDo, PartialTypeSignatures #-}
{-# OPTIONS_GHC -Wno-partial-type-signatures #-}

module Test.Picker where

import Prelude hiding (take)
import System.Random (RandomGen, next)
import Control.Monad.State
import Data.Number.Nat (Nat(..), take)
import GHC.Generics
import Data.Maybe
import Control.Monad.Trans.Maybe

class Monad m => MonadPicker m where
  -- | Pick a random element.
  runPicker :: RandomGen g => m a -> {-| maximal search depth -} Nat -> State g (Maybe a)
  -- | Choose an element of the list.
  choose :: [m a] -> m a
  -- | Choose an element of one of the lists; decrement the depth.
  chooseDeeper ::
    [m a] ->
    [m a] {-^ These options are only considered when there is some depth left. -} ->
    m a
evalPicker :: (MonadPicker m, RandomGen g) => m a -> g -> Nat -> Maybe a
evalPicker pa g d = fst $ runState (runPicker pa d) g
samplePicker :: (MonadPicker m, RandomGen g) => Nat -> m a -> g -> Nat -> [a]
samplePicker n pa g d = catMaybes $ fst $ runState (sequenceA $ take n $ repeat $ runPicker pa d) g

data Picker a where
  Picker :: (forall g . RandomGen g => Nat -> State g (Maybe a)) -> Picker a

deriving instance Functor Picker

instance Applicative Picker where
  pure a = Picker $ \ d -> runMaybeT $ return a
  Picker f <*> Picker a = Picker $ \ d -> runMaybeT $ MaybeT (f d) <*> MaybeT (a d)

instance Monad Picker where
  Picker a >>= f = Picker $ \ d -> runMaybeT $ do
    a' <- MaybeT $ a d
    let Picker fa = f a'
    MaybeT $ fa d
  fail msg = Picker $ \d -> state $ \g -> (Nothing, g)

instance MonadPicker Picker where
  runPicker (Picker a) = a
  choose mas = Picker $
    \d -> runMaybeT $ (MaybeT $ runThePicker 0) >>= (\r -> MaybeT $ runPicker (mas !! (r `mod` length mas)) d)
  chooseDeeper mas mbs = Picker $
    \d -> if d == 0
             then runPicker (choose mas :: Picker _) 0
             else runPicker (choose $ mas ++ mbs :: Picker _) (d - 1)

------------------------------------

class Pickable a where
  picker :: Picker a
  picker = Picker $ runThePicker
  runThePicker :: RandomGen g => {-| maximal search depth -} Nat -> State g (Maybe a)
  runThePicker = runPicker picker
  {-# MINIMAL picker | runThePicker #-}

pick :: (Pickable a, RandomGen g) => g -> Nat -> Maybe a
pick g d = evalPicker picker g d
sample :: (Pickable a, RandomGen g) => Nat -> g -> Nat -> [a]
sample n g d = samplePicker n picker g d

------------------------------------

instance Pickable Int where
  runThePicker d = Just <$> state next

instance Pickable () where
  picker = return ()

instance (Pickable a, Pickable b) => Pickable (a, b) where
  picker = (,) <$> picker <*> picker

instance Pickable Bool where
  picker = choose [return True, return False]

instance (Pickable a) => Pickable (Maybe a) where
  picker = choose $ return Nothing : (take 4 $ repeat $ Just <$> picker)

-----------------------------------