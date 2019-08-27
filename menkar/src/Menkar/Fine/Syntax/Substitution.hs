{-# LANGUAGE UndecidableInstances #-}

module Menkar.Fine.Syntax.Substitution where

import Menkar.Basic.Context

import Control.Exception.AssertFalse
import Data.Functor.Functor1
import Data.Functor.Coyoneda.NF
import Control.DeepSeq.Redone
import Data.Constraint.AlgebraicFunctor

import Data.Functor.Compose
import Control.Applicative
import GHC.Generics
import Data.Kind
import Data.Coerce
import Control.Lens

{-
-- | @substitute h fv = swallow (h <$> fv)@
class CanSwallow (f :: * -> *) (g :: * -> *) where
  substitute :: (w -> f v) -> g w -> g v
  default substitute :: (Generic1 g, CanSwallow f (Rep1 g)) => (w -> f v) -> g w -> g v
  substitute h = to1 . substitute h . from1
  
  swallow :: g (f v) -> g v
  swallow = substitute id
-}

-- | @substitute h fv = swallow (h <$> fv)@
class CanSwallow (f :: * -> *) (g :: * -> *) where
  substitute :: forall v w .
    (DeBruijnLevel v, DeBruijnLevel w) =>
    (w -> f v) -> g w -> g v
  default substitute :: forall v w .
    (DeBruijnLevel v, DeBruijnLevel w, Generic1 g, CanSwallow f (Rep1 g)) =>
    (w -> f v) -> g w -> g v
  substitute h = to1 . substitute h . from1
  
substLast :: forall f g v .
  (DeBruijnLevel v, DBPointed f, CanSwallow f g) =>
  f v -> g (VarExt v) -> g v
substLast fv gextv = substitute aux gextv
  where aux :: VarExt v -> f v
        aux (VarWkn v) = dbpure v
        aux (VarLast) = fv
        
-------------------------------------------

instance (CanSwallow f g, Functor h) => CanSwallow f (Compose h g) where
  substitute h (Compose hgx) = Compose (substitute h <$> hgx)

-------------------------------------------

{-| @'Expr' e v@ is the type of expressions with variables from 'v' and non-variables from 'e v'.
    The constraints @('Functor' e, 'Swallows' e ('Expr' e))@ should hold.
    The idea is that any other syntactic class can be defined as @Compose g (Expr e)@, for some functor g.
    Then automatically, @Compose g (Expr e)@ is a swallowing functor.
-}
data Expr (e :: * -> *) (v :: *) =
  Var !v
  | Expr (e v)
  deriving (Functor, Foldable, Traversable, Generic1, AlgebraicFunctor c)
deriving instance (Show v, Show (e v)) => Show (Expr e v)
deriving instance (Eq v, Eq (e v)) => Eq (Expr e v)
deriving instance (NFData_ e) => NFData_ (Expr e)

instance CanSwallow (Expr e) e => CanSwallow (Expr e) (Expr e) where
  substitute h (Var w) = h w
  substitute h (Expr ew) = Expr (substitute h ew)
  --swallow (Var ev) = ev
  --swallow (Expr eev) = Expr (swallow eev)

instance DBPointed (Expr e) where
  dbpure = Var
  
--instance (Functor e, CanSwallow (Expr e) e) => Applicative (Expr e) where
--  pure = Var
--  tf <*> tv = substitute (<$> tv) tf

--instance (Functor e, CanSwallow (Expr e) e) => Monad (Expr e) where
--  (>>=) = flip substitute

-------------------------------------------

{-| @'Expr' e v@ is the type of expressions with variables from 'v' and non-variables from 'e v'.
    The constraints @('Functor' e, 'Swallows' e ('Expr' e))@ should hold.
    The idea is that any other syntactic class can be defined as @Compose g (Expr e)@, for some functor g.
    Then automatically, @Compose g (Expr e)@ is a swallowing functor.
-}
data Expr2 (e :: ka -> * -> *) (a :: ka) (v :: *) =
  Var2 !v
  | Expr2 (e a v)
  deriving (Functor, Foldable, Traversable, Generic1, AlgebraicFunctor c)
deriving instance (NFData_ (e a)) => NFData_ (Expr2 e a)
--deriving instance (Eq v, Eq (e a v), Functor (e a)) => Eq (Expr2 e a v)

instance CanSwallow (Expr2 e a) (e a) => CanSwallow (Expr2 e a) (Expr2 e a) where
  substitute h (Var2 w) = h w
  substitute h (Expr2 ew) = Expr2 $ substitute h ew
  --swallow (Var2 ev) = ev
  --swallow (Expr2 eev) = Expr2 (swallow eev)

instance DBPointed (Expr2 e a) where
  dbpure = Var2

--instance (Functor (e a), CanSwallow (Expr2 e a) (e a)) => Applicative (Expr2 e a) where
--  pure = Var2
--  (tf :: Expr2 e a (u -> v)) <*> (tu :: Expr2 e a u) = substitute (<$> tu) tf
--  --tf <*> tv = swallow $ fmap (<$> tv) tf

--instance (Functor (e a), CanSwallow (Expr2 e a) (e a)) => Monad (Expr2 e a) where
--  (>>=) = flip substitute

substLast2 :: (DeBruijnLevel v, Functor f, CanSwallow (Expr2 e a) f) => Expr2 e a v -> f (VarExt v) -> f v
substLast2 = substLast

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
  --swallow = absurd1

-- unit
instance CanSwallow e U1 where
  substitute h U1 = U1
  --swallow U1 = U1

instance CanSwallow e f => CanSwallow e (Rec1 f) where
  substitute h (Rec1 fx) = Rec1 $ substitute h fx
  --swallow (Rec1 fex) = Rec1 $ swallow fex

instance CanSwallow e (K1 i c) where
  substitute h (K1 k) = K1 k
  --swallow (K1 k) = K1 k

instance CanSwallow e f => CanSwallow e (M1 i c f) where
  substitute h (M1 fx) = M1 $ substitute h fx
  --swallow (M1 fex) = M1 $ swallow fex

instance (CanSwallow e l, CanSwallow e r) => CanSwallow e (l :+: r) where
  substitute h (L1 lx) = L1 $ substitute h lx
  substitute h (R1 rx) = R1 $ substitute h rx
  --swallow (L1 lex) = L1 (swallow lex)
  --swallow (R1 rex) = R1 (swallow rex)

instance (CanSwallow e f, CanSwallow e g) => CanSwallow e (f :*: g) where
  substitute h (fx :*: gx) = substitute h fx :*: substitute h gx
  --swallow (fex :*: gex) = swallow fex :*: swallow gex

{-
instance (CanSwallow e h, Functor h, Traversable g, Applicative e) => CanSwallow e (h :.: g) where
  substitute h (Comp1 hgx) = Comp1 $ substitute (traverse h) hgx
  swallow (Comp1 hgex) = Comp1 $ substitute sequenceA hgex
-}
instance (CanSwallow e h, DBFunctor h, DBPointed e, DBFunctor e, DBMonoTraversable g) => CanSwallow e (h :.: g) where
  substitute h (Comp1 hgv) = Comp1 $ substitute (dbmonoTraverse h) hgv

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
instance (Functor h, CanSwallow e h) => CanSwallow e (DBCoyoneda h) where
  --swallow (DBCoyoneda q hx) = Coyoneda id $ substitute q hx
  substitute h (DBCoyoneda q hx) = DBCoyoneda id $ substitute (h . q) hx

coy :: (DeBruijnLevel v) => f v -> DBCoyoneda f v
coy = liftDBCoyoneda

uncoy :: (DeBruijnLevel v, DBFunctor f) => DBCoyoneda f v -> f v
uncoy = lowerDBCoyoneda

hoistCoy ::
  (forall x . DeBruijnLevel x => f x -> g x) ->
  (DeBruijnLevel a => DBCoyoneda f a -> DBCoyoneda g a)
hoistCoy = hoistDBCoyoneda
hoistCoyLens :: forall m f g . (Functor m) =>
  (forall x . (DeBruijnLevel x) => f x -> m (g x)) ->
  (forall a . (DeBruijnLevel a) => DBCoyoneda f a -> m (DBCoyoneda g a))
hoistCoyLens h (DBCoyoneda (q :: b -> a) fb) = DBCoyoneda q <$> mgb
  where mgb = h fb

cutCoy :: (DBFunctor f, DeBruijnLevel x, DeBruijnLevel y) => (f x -> g y) -> DBCoyoneda f x -> DBCoyoneda g y
cutCoy f = coy . f . uncoy
cutCoyLens :: forall m f g . (Functor m, DBFunctor f) =>
  (forall a . (DeBruijnLevel a) => f a -> m (g a)) ->
  (forall a . (DeBruijnLevel a) => DBCoyoneda f a -> m (DBCoyoneda g a))
cutCoyLens h = fmap coy . h . uncoy

-- | To understand this, consider what happens for @Compose [] Maybe@.
popCoy :: forall g f x . (Functor g) =>
  DBCoyoneda (Compose g f) x -> Compose g (DBCoyoneda f) x
popCoy (DBCoyoneda (q :: y -> x) (Compose (gfy :: g (f y)))) =
  Compose $ DBCoyoneda (q :: y -> x) <$> gfy

-- | To understand this, consider what happens for @[] :.: Maybe@.
copopCoy :: forall g f x . (DBFunctor f, forall v . (DeBruijnLevel v) => DeBruijnLevel (f v)) =>
  DBCoyoneda (g :.: f) x -> ((DBCoyoneda g) :.: f) x
copopCoy (DBCoyoneda (q :: y -> x) (Comp1 (gfy :: g (f y)))) =
  Comp1 $ DBCoyoneda (rename q :: f y -> f x) gfy
-- | It is atypical to need this function.
copopCoy' :: forall g f x . (DBFunctor f, forall v . (DeBruijnLevel v) => DeBruijnLevel (f v)) =>
  DBCoyoneda (Compose g f) x -> Compose (DBCoyoneda g) f x
copopCoy' (DBCoyoneda q (Compose gfy)) =
  Compose $ DBCoyoneda (rename q) gfy

pattern Coy x <- (lowerDBCoyoneda -> x)
  where Coy x = coy x
{-# COMPLETE Coy #-}
