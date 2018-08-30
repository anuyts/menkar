{-# LANGUAGE GADTs, DeriveFunctor, StandaloneDeriving, RankNTypes, ApplicativeDo, PartialTypeSignatures #-}
{-# OPTIONS_GHC -Wno-partial-type-signatures #-}

module Test.Picker where

import Prelude hiding ((!!), take)
import System.Random (RandomGen, next)
import Control.Monad.State
import Data.List.NonEmpty (NonEmpty(..), (!!))
import Data.Number.Nat (Nat(..), take)

class Monad m => MonadPicker m where
  -- | Pick a random element.
  pick :: RandomGen g => m a -> {-| maximal search depth -} Nat -> State g a
  -- | Choose an element of the list.
  choose :: NonEmpty (m a) -> m a
  -- | Choose an element of one of the lists; decrement the depth.
  chooseDeeper ::
    NonEmpty (m a) ->
    [m a] {-^ These options are only considered when there is some depth left. -} ->
    m a
pickLast :: (MonadPicker m, RandomGen g) => m a -> g -> Nat -> a
pickLast pa g d = fst $ runState (pick pa d) g
sample :: (MonadPicker m, RandomGen g) => Nat -> m a -> g -> Nat -> [a]
sample n pa g d = fst $ runState (sequenceA $ take n $ repeat $ pick pa d) g

data Picker a where
  Picker :: (forall g . RandomGen g => Nat -> State g a) -> Picker a

deriving instance Functor Picker

instance Applicative Picker where
  pure a = Picker $ \ d -> return a
  Picker f <*> Picker a = Picker $ \ d -> f d <*> a d

instance Monad Picker where
  Picker a >>= f = Picker $ \ d -> do
    a' <- a d
    let Picker fa = f a'
    fa d

instance MonadPicker Picker where
  pick (Picker a) d = a d
  choose mas = Picker $
    \d -> pick_ 0 >>= (\r -> pick (mas !! (r `mod` length mas)) d)
  chooseDeeper mas@(mahd :| matl) mbs = Picker $
    \d -> if d == 0
             then pick (choose mas :: Picker _) 0
             else pick (choose $mahd :| (matl ++ mbs) :: Picker _) (d - 1)

------------------------------------

class Pickable a where
  picker :: Picker a
  picker = Picker $ pick_
  pick_ :: RandomGen g => {-| maximal search depth -} Nat -> State g a
  pick_ = pick picker
  {-# MINIMAL picker | pick_ #-}

pickLast_ :: (Pickable a, RandomGen g) => g -> Nat -> a
pickLast_ g d = pickLast picker g d
sample_ :: (Pickable a, RandomGen g) => Nat -> g -> Nat -> [a]
sample_ n g d = sample n picker g d

------------------------------------

instance Pickable Int where
  pick_ d = state next

instance Pickable () where
  picker = return ()

instance (Pickable a, Pickable b) => Pickable (a, b) where
  picker = (,) <$> picker <*> picker

instance Pickable Bool where
  picker = choose (return True :| [return False])

instance (Pickable a) => Pickable (Maybe a) where
  picker = choose $ return Nothing :| (take 4 $ repeat $ Just <$> picker)
