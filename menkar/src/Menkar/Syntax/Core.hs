{-# LANGUAGE MultiParamTypeClasses, PolyKinds, DataKinds, TypeFamilies, RankNTypes, ConstraintKinds, GADTs,
FlexibleInstances, TypeInType, TypeOperators #-}

module Menkar.Syntax.Core where

import Data.Kind
import Data.Type.Natural (Nat(..))
import Data.Maybe
import Data.Monoid

data Leq (m :: Nat) (n :: Nat) where
  LeqEq :: Leq m m
  LeqStep :: Leq m n -> Leq m (S n)

class (:<=) (m :: Nat) (n :: Nat) where
  proveLeq :: Leq m n

instance m :<= m where
  proveLeq = LeqEq

instance (m :<= n) => (m :<= S n) where
  proveLeq = LeqStep proveLeq

-------------------------------------------

{-| @'Term' op '(n, cl) v@ is the type of terms of syntactic class @cl@, built with operators from @op@,
    and @n@ free variables from @v@.

    Here, @'Nothing@ is the syntactic class that variables are part of, and other classes are of the form @'Just c@.

    Here, @op arityclasses cl@ is the type of operators generating terms of syntactic class @cl@. The length of
    @arityclasses@ gives the number of arguments the operator takes. Each entry @'(n, cl)@ states that an argument has
    arity @n@ (can use @n@ additional variables) and should belong to syntactic class @cl@.
-}
data Term (op :: [(Nat, Maybe k)] -> Maybe k -> *) (cl :: Maybe k) (v :: *) :: * where
  Var :: v -> Term op Nothing v
  Term :: op arityclasses cl -> Args op arityclasses v -> Term op cl v

data OpenTerm (op :: [(Nat, Maybe k)] -> Maybe k -> *) (arityclass :: (Nat, Maybe k)) (v :: *) :: * where
  Closed :: Term op cl v -> OpenTerm op '(Z, cl) v
  Abs :: OpenTerm op '(arity, cl) (Maybe v) -> OpenTerm op '(S arity, cl) v

data Args (op :: [(Nat, Maybe k)] -> Maybe k -> *) (arityclasses :: [(Nat, Maybe k)]) (v :: *) :: * where
  EndArgs :: Args op '[] v
  (:..) :: OpenTerm op '(arity, cl) v -> Args op arityclasses v -> Args op ('(arity, cl) ': arityclasses) v

-------------------------------------------

instance Functor (Term op cl) where
  fmap f (Var v) = Var $ f v
  fmap f (Term d args) = Term d (fmap f args)

instance Functor (OpenTerm op arityclass) where
  fmap f (Closed t) = Closed $ fmap f t
  fmap f (Abs t) = Abs $ fmap (fmap f) t

instance Functor (Args op arityclasses) where
  fmap f EndArgs = EndArgs
  fmap f (arg :.. args) = fmap f arg :.. fmap f args

-------------------------------------------

class Swallows (beast :: * -> *) (food :: * -> *) where
  swallow :: beast (food v) -> beast v

instance Swallows (Term op cl) (Term op Nothing) where
  swallow (Var tv) = tv
  swallow (Term op args) = Term op $ swallow args

instance Swallows (OpenTerm op '(n, cl)) (Term op Nothing) where
  swallow (Closed ttv) = Closed $ swallow ttv
  swallow (Abs ttv) = Abs $ swallow $ fmap (fromMaybe (Var Nothing) . (fmap $ fmap Just)) $ ttv

instance Swallows (Args op arityclasses) (Term op Nothing) where
  swallow EndArgs = EndArgs
  swallow (ttv :.. atv) = swallow ttv :.. swallow atv

-------------------------------------------

instance Applicative (Term op Nothing) where
  pure = Var
  tf <*> tv = swallow $ fmap (<$> tv) tf

instance Monad (Term op Nothing) where
  tv >>= f = swallow $ f <$> tv

-------------------------------------------

instance Foldable (Term op cl) where
  foldMap f (Var v) = f v
  foldMap f (Term op args) = foldMap f args

instance Foldable (OpenTerm op '(arity, cl)) where
  foldMap f (Closed tv) = foldMap f tv
  foldMap f (Abs tv) = foldMap (fromMaybe mempty . fmap f) tv

instance Foldable (Args op arityclasses) where
  foldMap f EndArgs = mempty
  foldMap f (tv :.. av) = foldMap f tv <> foldMap f av

-------------------------------------------

instance Traversable (Term op cl) where
  sequenceA (Var fv) = Var <$> fv
  sequenceA (Term op args) = Term op <$> sequenceA args

instance Traversable (OpenTerm op '(arity, cl)) where
  sequenceA (Closed tfv) = Closed <$> sequenceA tfv
  sequenceA (Abs tfv) = Abs <$> (sequenceA $ fmap sequenceA $ tfv)

instance Traversable (Args op arityclasses) where
  sequenceA EndArgs = pure EndArgs
  sequenceA (tfv :.. afv) = (:..) <$> sequenceA tfv <*> sequenceA afv

-------------------------------------------

type family Repeat (x :: k) (n :: Nat) :: [k]
type instance Repeat x Z = '[]
type instance Repeat x (S n) = x ': Repeat x n
