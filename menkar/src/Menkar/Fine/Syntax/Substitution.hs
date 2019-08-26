{-# LANGUAGE UndecidableInstances #-}

module Menkar.Fine.Syntax.Substitution where

import Menkar.Basic.Context.Variable

import Control.Exception.AssertFalse
import Data.Functor.Functor1
import Data.Functor.Coyoneda.NF
import Control.DeepSeq.Redone

import Data.Functor.Compose
import Control.Applicative
import GHC.Generics
import Data.Kind
import Data.Coerce

-- | @substitute h fv = swallow (h <$> fv)@
class CanSwallow (f :: * -> *) (g :: * -> *) where
  substitute :: (w -> f v) -> g w -> g v
  default substitute :: (Generic1 g, CanSwallow f (Rep1 g)) => (w -> f v) -> g w -> g v
  substitute h = to1 . substitute h . from1
  
  swallow :: g (f v) -> g v
  swallow = substitute id

substLast :: forall f g v . (Functor g, Applicative f, CanSwallow f g) => f v -> g (VarExt v) -> g v
substLast fv gextv = substitute aux gextv
  where aux :: VarExt v -> f v
        aux (VarWkn v) = pure v
        aux (VarLast) = fv

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
  substitute h (Compose hgx) = Compose (substitute h <$> hgx)

-------------------------------------------

{-| @'Expr' e v@ is the type of expressions with variables from 'v' and non-variables from 'e v'.
    The constraints @('Functor' e, 'Swallows' e ('Expr' e))@ should hold.
    The idea is that any other syntactic class can be defined as @Compose g (Expr e)@, for some functor g.
    Then automatically, @Compose g (Expr e)@ is a swallowing functor.
-}
data Expr (e :: * -> *) (v :: *) =
  Var v
  | Expr (e v)
  deriving (Functor, Foldable, Traversable, Generic1)
deriving instance (Show v, Show (e v)) => Show (Expr e v)
deriving instance (Eq v, Eq (e v)) => Eq (Expr e v)
deriving instance (NFData_ e) => NFData_ (Expr e)

instance CanSwallow (Expr e) e => CanSwallow (Expr e) (Expr e) where
  substitute h (Var w) = h w
  substitute h (Expr ew) = Expr (substitute h ew)
  swallow (Var ev) = ev
  swallow (Expr eev) = Expr (swallow eev)

instance (Functor e, CanSwallow (Expr e) e) => Applicative (Expr e) where
  pure = Var
  tf <*> tv = substitute (<$> tv) tf

instance (Functor e, CanSwallow (Expr e) e) => Monad (Expr e) where
  (>>=) = flip substitute

-------------------------------------------

{-| @'Expr' e v@ is the type of expressions with variables from 'v' and non-variables from 'e v'.
    The constraints @('Functor' e, 'Swallows' e ('Expr' e))@ should hold.
    The idea is that any other syntactic class can be defined as @Compose g (Expr e)@, for some functor g.
    Then automatically, @Compose g (Expr e)@ is a swallowing functor.
-}
data Expr2 (e :: ka -> * -> *) (a :: ka) (v :: *) =
  Var2 v
  | Expr2 (e a v)
  deriving (Functor, Foldable, Traversable, Generic1)
deriving instance (NFData_ (e a)) => NFData_ (Expr2 e a)
--deriving instance (Eq v, Eq (e a v), Functor (e a)) => Eq (Expr2 e a v)

instance CanSwallow (Expr2 e a) (e a) => CanSwallow (Expr2 e a) (Expr2 e a) where
  substitute h (Var2 w) = h w
  substitute h (Expr2 ew) = Expr2 $ substitute h ew
  swallow (Var2 ev) = ev
  swallow (Expr2 eev) = Expr2 (swallow eev)

instance (Functor (e a), CanSwallow (Expr2 e a) (e a)) => Applicative (Expr2 e a) where
  pure = Var2
  (tf :: Expr2 e a (u -> v)) <*> (tu :: Expr2 e a u) = substitute (<$> tu) tf
  --tf <*> tv = swallow $ fmap (<$> tv) tf

instance (Functor (e a), CanSwallow (Expr2 e a) (e a)) => Monad (Expr2 e a) where
  (>>=) = flip substitute

substLast2 :: (Functor f, CanSwallow (Expr2 e a) f) => Expr2 e a v -> f (VarExt v) -> f v
substLast2 ev fextv = substitute substLast' $ fextv
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
  substitute h = absurd1
  swallow = absurd1

-- unit
instance CanSwallow e U1 where
  substitute h U1 = U1
  swallow U1 = U1

instance CanSwallow e f => CanSwallow e (Rec1 f) where
  substitute h (Rec1 fx) = Rec1 $ substitute h fx
  swallow (Rec1 fex) = Rec1 $ swallow fex

instance CanSwallow e (K1 i c) where
  substitute h (K1 k) = K1 k
  swallow (K1 k) = K1 k

instance CanSwallow e f => CanSwallow e (M1 i c f) where
  substitute h (M1 fx) = M1 $ substitute h fx
  swallow (M1 fex) = M1 $ swallow fex

instance (CanSwallow e l, CanSwallow e r) => CanSwallow e (l :+: r) where
  substitute h (L1 lx) = L1 $ substitute h lx
  substitute h (R1 rx) = R1 $ substitute h rx
  swallow (L1 lex) = L1 (swallow lex)
  swallow (R1 rex) = R1 (swallow rex)

instance (CanSwallow e f, CanSwallow e g) => CanSwallow e (f :*: g) where
  substitute h (fx :*: gx) = substitute h fx :*: substitute h gx
  swallow (fex :*: gex) = swallow fex :*: swallow gex

instance (CanSwallow e h, Functor h, Traversable g, Applicative e) => CanSwallow e (h :.: g) where
  substitute h (Comp1 hgx) = Comp1 $ substitute (traverse h) hgx
  swallow (Comp1 hgex) = Comp1 $ substitute sequenceA hgex

--------------------------------------------

{-
data Syn v = War v | App (Syn v) (Syn v) | Lam (Compose Syn Maybe v)

instance Functor Syn where
  fmap f (War v) = War $ f v
  fmap f (App fv fw) = App (fmap f fv) (fmap f fw)
  fmap f (Lam fv) = Lam $ fmap f fv

deriving instance Generic1 Syn
-}

--------------------------------------------

{-| Coyoneda fuses fmaps, making stuff more efficient. -}
instance (Functor h, CanSwallow e h) => CanSwallow e (Coyoneda h) where
  swallow (Coyoneda q hx) = Coyoneda id $ substitute q hx
  substitute h (Coyoneda q hx) = Coyoneda id $ substitute (h . q) hx

coy :: f x -> Coyoneda f x
coy = liftCoyoneda

uncoy :: (Functor f) => Coyoneda f x -> f x
uncoy = lowerCoyoneda

hoistCoy :: (Functor f, Functor g) => (forall x . f x -> g x) -> (Coyoneda f a -> Coyoneda g a)
hoistCoy = hoistCoyoneda
hoistCoyLens :: forall m f g a . (Functor m, Functor f, Functor g) =>
  (forall x . f x -> m (g x)) ->
  Coyoneda f a ->
  m (Coyoneda g a)
hoistCoyLens h (Coyoneda (q :: b -> a) fb) = Coyoneda q <$> mgb
  where mgb = h fb

cutCoy :: (Functor f) => (f x -> g y) -> Coyoneda f x -> Coyoneda g y
cutCoy f = coy . f . uncoy
cutCoyLens :: forall m f g a . (Functor m, Functor f) => (f a -> m (g a)) -> Coyoneda f a -> m (Coyoneda g a)
cutCoyLens h = fmap coy . h . uncoy

-- | To understand this, consider what happens for @Compose [] Maybe@.
popCoy :: forall g f x . (Functor f, Functor g) => Coyoneda (Compose g f) x -> Compose g (Coyoneda f) x
popCoy (Coyoneda (q :: y -> x) (Compose (gfy :: g (f y)))) =
  Compose $ Coyoneda (q :: y -> x) <$> gfy

-- | To understand this, consider what happens for @[] :.: Maybe@.
copopCoy :: forall g f x . (Functor f, Functor g) => Coyoneda (g :.: f) x -> ((Coyoneda g) :.: f) x
copopCoy (Coyoneda (q :: y -> x) (Comp1 (gfy :: g (f y)))) =
  Comp1 $ Coyoneda (fmap q :: f y -> f x) gfy
-- | It is atypical to need this function.
copopCoy' :: forall g f x . (Functor f, Functor g) => Coyoneda (Compose g f) x -> Compose (Coyoneda g) f x
copopCoy' (Coyoneda q (Compose gfy)) =
  Compose $ Coyoneda (fmap q) gfy

pattern Coy x <- (lowerCoyoneda -> x)
  where Coy x = coy x
{-# COMPLETE Coy #-}
