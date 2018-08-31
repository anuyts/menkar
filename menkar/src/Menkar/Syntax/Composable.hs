{-# LANGUAGE UndecidableInstances #-}

module Menkar.Syntax.Composable where

import Data.Functor.Compose
import Control.Applicative
import GHC.Generics

class Swallows (g :: * -> *) (f :: * -> *) where
  swallow :: g (f v) -> g v
  default swallow :: (Generic1 g, Swallows (Rep1 g) f) => g (f v) -> g v
  swallow = to1 . swallow . from1

newtype Precompose g f x = Precompose {getPrecompose :: (g (f x))}

deriving instance (Functor g, Functor f) => Functor (Precompose g f)
deriving instance (Foldable g, Foldable f) => Foldable (Precompose g f)
deriving instance (Traversable g, Traversable f) => Traversable (Precompose g f)

instance (Applicative g, Applicative f) => Applicative (Precompose g f) where
  pure x = Precompose $ pure . pure $ x
  Precompose gff <*> Precompose gfx = Precompose ((<*>) <$> gff <*> gfx)

instance (Swallows g f, Functor h) => Swallows (Compose h g) f where
  swallow (Compose hgfx) = Compose (fmap swallow hgfx)

instance (Swallows h f, Functor h, Traversable g, Applicative f) => Swallows (Precompose h g) f where
  swallow (Precompose hgfx) = Precompose $ swallow $ fmap sequenceA hgfx

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

instance Swallows e (Expr e) => Swallows (Expr e) (Expr e) where
  swallow (Var ev) = ev
  swallow (Expr eev) = Expr (swallow eev)

instance (Functor e, Swallows e (Expr e)) => Applicative (Expr e) where
  pure = Var
  tf <*> tv = swallow $ fmap (<$> tv) tf

instance (Functor e, Swallows e (Expr e)) => Monad (Expr e) where
  tv >>= f = swallow $ f <$> tv

--------------------------------------------

-- void
instance Swallows V1 e where
  swallow contradiction = undefined

-- unit
instance Swallows U1 e where
  swallow U1 = U1

instance Swallows f e => Swallows (Rec1 f) e where
  swallow (Rec1 fex) = Rec1 $ swallow fex

instance Swallows (K1 i c) e where
  swallow (K1 k) = K1 k

instance Swallows f e => Swallows (M1 i c f) e where
  swallow (M1 fex) = M1 $ swallow fex

instance (Swallows l e, Swallows r e) => Swallows (l :+: r) e where
  swallow (L1 lex) = L1 (swallow lex)
  swallow (R1 rex) = R1 (swallow rex)

instance (Swallows f e, Swallows g e) => Swallows (f :*: g) e where
  swallow (fex :*: gex) = swallow fex :*: swallow gex

instance (Swallows h e, Functor h, Traversable g, Applicative e) => Swallows (h :.: g) e where
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
