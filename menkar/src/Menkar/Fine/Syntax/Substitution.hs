{-# LANGUAGE UndecidableInstances #-}

module Menkar.Fine.Syntax.Substitution where

import Menkar.Basic.Context.Variable
import Control.Exception.AssertFalse

import Data.Functor.Compose
import Control.Applicative
import GHC.Generics
import Data.Kind

class CanSwallow (f :: * -> *) (g :: * -> *) where
  swallow :: g (f v) -> g v
  default swallow :: (Generic1 g, CanSwallow f (Rep1 g)) => g (f v) -> g v
  swallow = to1 . swallow . from1

{-
newtype Precompose g f x = Precompose {getPrecompose :: (g (f x))}

deriving instance (Functor g, Functor f) => Functor (Precompose g f)
deriving instance (Foldable g, Foldable f) => Foldable (Precompose g f)
deriving instance (Traversable g, Traversable f) => Traversable (Precompose g f)

instance (Applicative g, Applicative f) => Applicative (Precompose g f) where
  pure x = Precompose $ pure . pure $ x
  Precompose gff <*> Precompose gfx = Precompose ((<*>) <$> gff <*> gfx)

instance (CanSwallow f h, Functor h, Traversable g, Applicative f) => CanSwallow f (Precompose h g) where
  swallow (Precompose hgfx) = Precompose $ swallow $ fmap sequenceA hgfx
-}

instance (CanSwallow f g, Functor h) => CanSwallow f (Compose h g) where
  swallow (Compose hgfx) = Compose (fmap swallow hgfx)

-------------------------------------------

{-| @'Expr' e v@ is the type of expressions with variables from 'v' and non-variables from 'e v'.
    The constraints @('Functor' e, 'Swallows' e ('Expr' e))@ should hold.
    The idea is that any other syntactic class can be defined as @Compose g (Expr e)@, for some functor g.
    Then automatically, @Compose g (Expr e)@ is a swallowing functor.
-}
data Expr (e :: * -> *) (v :: *) =
  Var v
  | Expr (e v)
  deriving (Functor, Foldable, Traversable)
deriving instance (Show v, Show (e v)) => Show (Expr e v)
deriving instance (Eq v, Eq (e v)) => Eq (Expr e v)

instance CanSwallow (Expr e) e => CanSwallow (Expr e) (Expr e) where
  swallow (Var ev) = ev
  swallow (Expr eev) = Expr (swallow eev)

instance (Functor e, CanSwallow (Expr e) e) => Applicative (Expr e) where
  pure = Var
  tf <*> tv = swallow $ fmap (<$> tv) tf

instance (Functor e, CanSwallow (Expr e) e) => Monad (Expr e) where
  tv >>= f = swallow $ f <$> tv

-------------------------------------------

{-| @'Expr' e v@ is the type of expressions with variables from 'v' and non-variables from 'e v'.
    The constraints @('Functor' e, 'Swallows' e ('Expr' e))@ should hold.
    The idea is that any other syntactic class can be defined as @Compose g (Expr e)@, for some functor g.
    Then automatically, @Compose g (Expr e)@ is a swallowing functor.
-}
data Expr2 (e :: ka -> * -> *) (a :: ka) (v :: *) =
  Var2 v
  | Expr2 (e a v)
  deriving (Functor, Foldable, Traversable)
deriving instance (Eq v, Eq (e a v)) => Eq (Expr2 e a v)

instance CanSwallow (Expr2 e a) (e a) => CanSwallow (Expr2 e a) (Expr2 e a) where
  swallow (Var2 ev) = ev
  swallow (Expr2 eev) = Expr2 (swallow eev)

instance (Functor (e a), CanSwallow (Expr2 e a) (e a)) => Applicative (Expr2 e a) where
  pure = Var2
  tf <*> tv = swallow $ fmap (<$> tv) tf

instance (Functor (e a), CanSwallow (Expr2 e a) (e a)) => Monad (Expr2 e a) where
  tv >>= f = swallow $ f <$> tv

substLast2 :: (Functor f, CanSwallow (Expr2 e a) f) => Expr2 e a v -> f (VarExt v) -> f v
substLast2 ev fextv = swallow $ substLast' <$> fextv
  where substLast' :: VarExt _ -> Expr2 _ _ _
        substLast' VarLast = ev
        substLast' (VarWkn v) = Var2 v

-------------------------------------------

{-
{-| @'Expr' e v@ is the type of expressions with variables from 'v' and non-variables from 'e v'.
    The constraints @('Functor' e, 'Swallows' e ('Expr' e))@ should hold.
    The idea is that any other syntactic class can be defined as @Compose g (Expr e)@, for some functor g.
    Then automatically, @Compose g (Expr e)@ is a swallowing functor.
-}
data Expr3 (e :: ka -> kb -> * -> *) (a :: ka) (b :: kb) (v :: *) =
  Var3 v
  | Expr3 (e a b v)
  deriving (Functor, Foldable, Traversable)
--deriving instance (Show v, Show (e a b v)) => Show (Expr3 e a b v)
deriving instance (Eq v, Eq (e a b v)) => Eq (Expr3 e a b v)

instance CanSwallow (Expr3 e a b) (e a b) => CanSwallow (Expr3 e a b) (Expr3 e a b) where
  swallow (Var3 ev) = ev
  swallow (Expr3 eev) = Expr3 (swallow eev)

instance (Functor (e a b), CanSwallow (Expr3 e a b) (e a b)) => Applicative (Expr3 e a b) where
  pure = Var3
  tf <*> tv = swallow $ fmap (<$> tv) tf

instance (Functor (e a b), CanSwallow (Expr3 e a b) (e a b)) => Monad (Expr3 e a b) where
  tv >>= f = swallow $ f <$> tv

substLast3 :: (Functor f, CanSwallow (Expr3 e a b) f) => Expr3 e a b v -> f (VarExt v) -> f v
substLast3 ev fextv = swallow $ substLast' <$> fextv
  where substLast' :: VarExt _ -> Expr3 _ _ _ _
        substLast' VarLast = ev
        substLast' (VarWkn v) = Var3 v
-}

--------------------------------------------

-- void
instance CanSwallow e V1 where
  swallow contradiction = undefined

-- unit
instance CanSwallow e U1 where
  swallow U1 = U1

instance CanSwallow e f => CanSwallow e (Rec1 f) where
  swallow (Rec1 fex) = Rec1 $ swallow fex

instance CanSwallow e (K1 i c) where
  swallow (K1 k) = K1 k

instance CanSwallow e f => CanSwallow e (M1 i c f) where
  swallow (M1 fex) = M1 $ swallow fex

instance (CanSwallow e l, CanSwallow e r) => CanSwallow e (l :+: r) where
  swallow (L1 lex) = L1 (swallow lex)
  swallow (R1 rex) = R1 (swallow rex)

instance (CanSwallow e f, CanSwallow e g) => CanSwallow e (f :*: g) where
  swallow (fex :*: gex) = swallow fex :*: swallow gex

instance (CanSwallow e h, Functor h, Traversable g, Applicative e) => CanSwallow e (h :.: g) where
  swallow (Comp1 hgex) = Comp1 $ swallow $ fmap sequenceA hgex

--------------------------------------------

{-
data Syn v = War v | App (Syn v) (Syn v) | Lam (Compose Syn Maybe v)

instance Functor Syn where
  fmap f (War v) = War $ f v
  fmap f (App fv fw) = App (fmap f fv) (fmap f fw)
  fmap f (Lam fv) = Lam $ fmap f fv

deriving instance Generic1 Syn
-}
