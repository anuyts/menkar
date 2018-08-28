{-# LANGUAGE MultiParamTypeClasses, PolyKinds, DataKinds, TypeFamilies, RankNTypes, ConstraintKinds, GADTs,
FlexibleInstances, TypeInType, TypeOperators #-}

module Menkar.Syntax.Codes where

import Data.Kind
import Data.Type.Natural (Nat(..))

{-| @'Term' def '(n, cl) v@ is the type of terms of syntactic class @cl@, built with operators from @def@,
    and @n@ free variables from @v@.

    Here, @'Nothing@ is the syntactic class that variables are part of, and other classes are of the form @'Just c@.

    Here, @def arityclasses cl@ is the type of operators generating terms of syntactic class @cl@. The length of
    @arityclasses@ gives the number of arguments the operator takes. Each entry @'(n, cl)@ states that an argument has
    arity @n@ (can use @n@ additional variables) and should belong to syntactic class @cl@.
-}
data Term (def :: [(Nat, Maybe *)] -> Maybe * -> *) (arityclass :: (Nat, Maybe *)) (v :: *) :: * where
  Var :: v -> Term def '(Z, Nothing) v
  Abs :: Term def '(arity, cl) (Maybe v) -> Term def '(S arity, cl) v
  Term :: def arityclasses cl -> Args def arityclasses v -> Term def '(Z, cl) v

data Args (def :: [(Nat, Maybe *)] -> Maybe * -> *) (arityclasses :: [(Nat, Maybe *)]) (v :: *) :: * where
  EndArgs :: Args def '[] v
  (:..) :: Term def '(arity, cl) v -> Args def arityclasses v -> Args def ('(arity, cl) ': arityclasses) v

instance Functor (Term def arityclass) where
  fmap f (Var v) = Var $ f v
  fmap f (Abs t) = Abs $ fmap (fmap f) t
  fmap f (Term d args) = Term d (fmap f args)

instance Functor (Args def arityclasses) where
  fmap f EndArgs = EndArgs
  fmap f (arg :.. args) = fmap f arg :.. fmap f args

class Swallows (beast :: * -> *) (food :: * -> *) where
  swallow :: beast (food v) -> beast v

instance Swallows (Term def '(n, cl)) (Term def '(n, Nothing)) where
  swallow (Var tv) = tv
  swallow ttv = _

{-
data OpLambdaApp fs where
  App :: OpLambdaApp [Identity, Identity]
-}

--TODO: use 'Either (r :: *) v' instead of '(f :: Traversable) v'

