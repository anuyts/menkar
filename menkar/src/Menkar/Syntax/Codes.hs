{-# LANGUAGE MultiParamTypeClasses, PolyKinds, DataKinds, TypeFamilies, RankNTypes, ConstraintKinds, GADTs,
FlexibleInstances, TypeInType, TypeOperators #-}

module Menkar.Syntax.Codes where

import Data.Kind
import Data.Type.Natural (Nat(..))

{-| @'Term' op '(n, cl) v@ is the type of terms of syntactic class @cl@, built with operators from @op@,
    and @n@ free variables from @v@.

    Here, @'Nothing@ is the syntactic class that variables are part of, and other classes are of the form @'Just c@.

    Here, @op arityclasses cl@ is the type of operators generating terms of syntactic class @cl@. The length of
    @arityclasses@ gives the number of arguments the operator takes. Each entry @'(n, cl)@ states that an argument has
    arity @n@ (can use @n@ additional variables) and should belong to syntactic class @cl@.
-}
data Term (op :: [(Nat, Maybe *)] -> Maybe * -> *) (arityclass :: (Nat, Maybe *)) (v :: *) :: * where
  Var :: v -> Term op '(Z, Nothing) v
  Abs :: Term op '(arity, cl) (Maybe v) -> Term op '(S arity, cl) v
  Term :: op arityclasses cl -> Args op arityclasses v -> Term op '(Z, cl) v

data Args (op :: [(Nat, Maybe *)] -> Maybe * -> *) (arityclasses :: [(Nat, Maybe *)]) (v :: *) :: * where
  EndArgs :: Args op '[] v
  (:..) :: Term op '(arity, cl) v -> Args op arityclasses v -> Args op ('(arity, cl) ': arityclasses) v

instance Functor (Term op arityclass) where
  fmap f (Var v) = Var $ f v
  fmap f (Abs t) = Abs $ fmap (fmap f) t
  fmap f (Term d args) = Term d (fmap f args)

instance Functor (Args op arityclasses) where
  fmap f EndArgs = EndArgs
  fmap f (arg :.. args) = fmap f arg :.. fmap f args

class Swallows (beast :: * -> *) (food :: * -> *) where
  swallow :: beast (food v) -> beast v

instance Swallows (Term op '(n, cl)) (Term op '(n, Nothing)) where
  swallow (Var tv) = tv
  swallow ttv = _

