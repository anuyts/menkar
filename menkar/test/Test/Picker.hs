{-# LANGUAGE GADTs, DeriveFunctor, StandaloneDeriving, RankNTypes, ApplicativeDo, PartialTypeSignatures #-}
{-# OPTIONS_GHC -Wno-partial-type-signatures #-}

module Test.Picker where

import Prelude hiding ((!!))
import System.Random (RandomGen, next)
import Control.Monad.State
import Data.List.NonEmpty hiding (length)
import Data.Number.Nat hiding (length)

class Monad m => MonadPicker m where
  -- | Pick a random element.
  pick :: RandomGen g => m a -> {-| maximal search depth -} Nat -> State g a
  -- | Choose an element of the list.
  choose :: NonEmpty a -> m a
  -- | Choose an element of one of the lists; decrement the depth.
  chooseDeeper ::
    NonEmpty a ->
    [a] {-^ These options are only considered when there is some depth left. -} ->
    m a
pickLast :: (MonadPicker m, RandomGen g) => m a -> g -> Nat -> a
pickLast pa g d = fst $ runState (pick pa d) g

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
  choose as = Picker $
    \d -> (\r -> as !! (r `mod` length as)) <$> pick_ 0
  chooseDeeper as@(ahd :| atl) bs = Picker $
    \d -> if d == 0
             then pick (choose as :: Picker _) 0
             else pick (choose $ahd :| (atl ++ bs) :: Picker _) (d - 1)

------------------------------------

class Pickable a where
  picker :: Picker a

pick_ :: (Pickable a, RandomGen g) => {-| maximal search depth -} Nat -> State g a
pick_ d = pick picker d
pickLast_ :: (Pickable a, RandomGen g) => g -> Nat -> a
pickLast_ g d = pickLast picker g d

------------------------------------

instance Pickable Int where
  picker = Picker $ \d -> state next

instance Pickable Bool where
  picker = choose (True :| [False])
