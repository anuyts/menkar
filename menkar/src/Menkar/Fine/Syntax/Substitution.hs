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
import Control.Monad
import Data.Foldable

-- | @substitute h fv = swallow (h <$> fv)@
class CanSwallow (f :: * -> *) (g :: * -> *) where
  substitute :: (w -> f v) -> g w -> g v
  default substitute :: (Generic1 g, CanSwallow f (Rep1 g)) => (w -> f v) -> g w -> g v
  substitute h = to1 . substitute h . from1
  
  {-# INLINE swallow #-}
  swallow :: g (f v) -> g v
  swallow = substitute id

{-# INLINE substLast #-}
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
  {-# INLINE substitute #-}

-------------------------------------------

{-| @'Expr' e v@ is the type of expressions with variables from 'v' and non-variables from 'e v'.
    The constraints @('Functor' e, 'Swallows' e ('Expr' e))@ should hold.
    The idea is that any other syntactic class can be defined as @Compose g (Expr e)@, for some functor g.
    Then automatically, @Compose g (Expr e)@ is a swallowing functor.
-}
data Expr (e :: * -> *) (v :: *) =
  Var !v
  | Expr (e v)
  deriving (Functor, Foldable, Traversable, Generic1)
deriving instance (Show v, Show (e v)) => Show (Expr e v)
deriving instance (Eq v, Eq (e v)) => Eq (Expr e v)
deriving instance (NFData_ e) => NFData_ (Expr e)

instance CanSwallow (Expr e) e => CanSwallow (Expr e) (Expr e) where
  {-# INLINE substitute #-}
  substitute h (Var w) = h w
  substitute h (Expr ew) = Expr (substitute h ew)
  {-# INLINE swallow #-}
  swallow (Var ev) = ev
  swallow (Expr eev) = Expr (swallow eev)

instance (Functor e, CanSwallow (Expr e) e) => Applicative (Expr e) where
  {-# INLINE pure #-}
  pure = Var
  {-# INLINE (<*>) #-}
  tf <*> tv = substitute (<$> tv) tf

instance (Functor e, CanSwallow (Expr e) e) => Monad (Expr e) where
  {-# INLINE (>>=) #-}
  (>>=) = flip substitute

-------------------------------------------

{-| @'Expr' e v@ is the type of expressions with variables from 'v' and non-variables from 'e v'.
    The constraints @('Functor' e, 'Swallows' e ('Expr' e))@ should hold.
    The idea is that any other syntactic class can be defined as @Compose g (Expr e)@, for some functor g.
    Then automatically, @Compose g (Expr e)@ is a swallowing functor.
-}
data Expr2 (e :: ka -> * -> *) (a :: ka) (v :: *) =
  Var2 !v
  | Expr2Cache
      (e a v)
      [v] {-^ Cache of @toList@ for the first argument. -}
  deriving (Functor)
instance Foldable (Expr2 e a) where
  foldMap h (Var2 v) = h v
  foldMap h (Expr2Cache ev vs) = foldMap h vs
instance Traversable (e a) => Traversable (Expr2 e a) where
  traverse h (Var2 v) = Var2 <$> h v
  traverse h (Expr2 ev) = Expr2 <$> traverse h ev
instance (NFData_ (e a)) => NFData_ (Expr2 e a) where
  rnf_ (Var2 v) = ()
  rnf_ (Expr2Cache ev vs) = rnf_ ev `seq` rnf_ vs
--deriving instance (Eq v, Eq (e a v), Functor (e a)) => Eq (Expr2 e a v)

pattern Expr2 :: (Foldable (e a)) => () => (e a v) -> Expr2 e a v
pattern Expr2 e <- Expr2Cache e _
  where Expr2 e = Expr2Cache e (toList e)
{-# COMPLETE Var2, Expr2 #-}

instance (Foldable (e a), CanSwallow (Expr2 e a) (e a)) => CanSwallow (Expr2 e a) (Expr2 e a) where
  substitute h (Var2 w) = h w
  substitute h (Expr2Cache ew ws) = Expr2Cache (substitute h ew) (toList . h =<< ws)
  {-# INLINE substitute #-}
  swallow (Var2 ev) = ev
  swallow (Expr2Cache eev evs) = Expr2Cache (swallow eev) (toList =<< evs)
  {-# INLINE swallow #-}

instance (Functor (e a), Foldable (e a), CanSwallow (Expr2 e a) (e a)) => Applicative (Expr2 e a) where
  pure = Var2
  {-# INLINE pure #-}
  (tf :: Expr2 e a (u -> v)) <*> (tu :: Expr2 e a u) = substitute (<$> tu) tf
  {-# INLINE (<*>) #-}
  --tf <*> tv = swallow $ fmap (<$> tv) tf

instance (Functor (e a), Foldable (e a), CanSwallow (Expr2 e a) (e a)) => Monad (Expr2 e a) where
  (>>=) = flip substitute
  {-# INLINE (>>=) #-}

-- Does not just refer to substLast, because here we avoid requiring applicativity by using Var2 instead of pure.
substLast2 :: (Functor f, CanSwallow (Expr2 e a) f) => Expr2 e a v -> f (VarExt v) -> f v
substLast2 ev fextv = substitute substLast' $ fextv
  where substLast' :: VarExt _ -> Expr2 _ _ _
        substLast' VarLast = ev
        substLast' (VarWkn v) = Var2 v
{-# INLINE substLast2 #-}

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
  {-# INLINE substitute #-}
  substitute h = absurd1
  {-# INLINE swallow #-}
  swallow = absurd1

-- unit
instance CanSwallow e U1 where
  {-# INLINE substitute #-}
  substitute h U1 = U1
  {-# INLINE swallow #-}
  swallow U1 = U1

instance CanSwallow e f => CanSwallow e (Rec1 f) where
  {-# INLINE substitute #-}
  substitute h (Rec1 fx) = Rec1 $ substitute h fx
  {-# INLINE swallow #-}
  swallow (Rec1 fex) = Rec1 $ swallow fex

instance CanSwallow e (K1 i c) where
  {-# INLINE substitute #-}
  substitute h (K1 k) = K1 k
  {-# INLINE swallow #-}
  swallow (K1 k) = K1 k

instance CanSwallow e f => CanSwallow e (M1 i c f) where
  {-# INLINE substitute #-}
  substitute h (M1 fx) = M1 $ substitute h fx
  {-# INLINE swallow #-}
  swallow (M1 fex) = M1 $ swallow fex

instance (CanSwallow e l, CanSwallow e r) => CanSwallow e (l :+: r) where
  {-# INLINE substitute #-}
  substitute h (L1 lx) = L1 $ substitute h lx
  substitute h (R1 rx) = R1 $ substitute h rx
  {-# INLINE swallow #-}
  swallow (L1 lex) = L1 (swallow lex)
  swallow (R1 rex) = R1 (swallow rex)

instance (CanSwallow e f, CanSwallow e g) => CanSwallow e (f :*: g) where
  {-# INLINE substitute #-}
  substitute h (fx :*: gx) = substitute h fx :*: substitute h gx
  {-# INLINE swallow #-}
  swallow (fex :*: gex) = swallow fex :*: swallow gex

instance (CanSwallow e h, Functor h, Traversable g, Applicative e) => CanSwallow e (h :.: g) where
  {-# INLINE substitute #-}
  substitute h (Comp1 hgx) = Comp1 $ substitute (uncoy . traverse (coy . h)) hgx
  {-# INLINE swallow #-}
  swallow (Comp1 hgex) = Comp1 $ substitute (uncoy . traverse coy) hgex

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
  {-# INLINE substitute #-}
  substitute h (Coyoneda q hx) = Coyoneda id $ substitute (h . q) hx
  {-# INLINE swallow #-}
  swallow (Coyoneda q hx) = Coyoneda id $ substitute q hx

{-# INLINE coy #-}
coy :: f x -> Coyoneda f x
coy = liftCoyoneda

{-# INLINE uncoy #-}
uncoy :: (Functor f) => Coyoneda f x -> f x
uncoy = lowerCoyoneda

{-# INLINE hoistCoy #-}
hoistCoy :: (Functor f, Functor g) => (forall x . f x -> g x) -> (Coyoneda f a -> Coyoneda g a)
hoistCoy = hoistCoyoneda
{-# INLINE hoistCoyLens #-}
hoistCoyLens :: forall m f g a . (Functor m, Functor f, Functor g) =>
  (forall x . f x -> m (g x)) ->
  Coyoneda f a ->
  m (Coyoneda g a)
hoistCoyLens h (Coyoneda (q :: b -> a) fb) = Coyoneda q <$> h fb

{-# INLINE cutCoy #-}
cutCoy :: (Functor f) => (f x -> g y) -> Coyoneda f x -> Coyoneda g y
cutCoy f = coy . f . uncoy
{-# INLINE cutCoyLens #-}
cutCoyLens :: forall m f g a . (Functor m, Functor f) => (f a -> m (g a)) -> Coyoneda f a -> m (Coyoneda g a)
cutCoyLens h = fmap coy . h . uncoy

-- | To understand this, consider what happens for @Compose [] Maybe@.
{-# INLINE popCoy #-}
popCoy :: forall g f x . (Functor f, Functor g) => Coyoneda (Compose g f) x -> Compose g (Coyoneda f) x
popCoy (Coyoneda (q :: y -> x) (Compose (gfy :: g (f y)))) =
  Compose $ Coyoneda (q :: y -> x) <$> gfy

-- | To understand this, consider what happens for @[] :.: Maybe@.
{-# INLINE copopCoy #-}
copopCoy :: forall g f x . (Functor f, Functor g) => Coyoneda (g :.: f) x -> ((Coyoneda g) :.: f) x
copopCoy (Coyoneda (q :: y -> x) (Comp1 (gfy :: g (f y)))) =
  Comp1 $ Coyoneda (fmap q :: f y -> f x) gfy
-- | It is atypical to need this function.
{-# INLINE copopCoy' #-}
copopCoy' :: forall g f x . (Functor f, Functor g) => Coyoneda (Compose g f) x -> Compose (Coyoneda g) f x
copopCoy' (Coyoneda q (Compose gfy)) =
  Compose $ Coyoneda (fmap q) gfy

pattern Coy x <- (lowerCoyoneda -> x)
  where Coy x = coy x
{-# COMPLETE Coy #-}

-------------------------------------------

data FreeSwallow t f v where
  Unsubstituted :: f v -> FreeSwallow t f v
  Substitute :: (v -> t w) -> FreeSwallow t f v -> FreeSwallow t f w
  Rename :: (v -> w) -> FreeSwallow t f v -> FreeSwallow t f w

{-# INLINE liftFS #-}
liftFS = Unsubstituted
{-# INLINE lowerFS #-}
lowerFS :: (CanSwallow t f, Monad t) => FreeSwallow t f v -> f v
lowerFS = lowerSubstituteFS pure

{-# INLINE liftSubstituteFS #-}
liftSubstituteFS = Substitute
{-# INLINE lowerSubstituteFS #-}
lowerSubstituteFS :: (CanSwallow t f, Monad t) => (v -> t w) -> FreeSwallow t f v -> f w
lowerSubstituteFS !h (Unsubstituted fv) = substitute h fv
lowerSubstituteFS !h (Substitute g sfv) = lowerSubstituteFS (g >=> h) sfv
lowerSubstituteFS !h (Rename g sfv) = lowerSubstituteFS (h . g) sfv

instance Functor (FreeSwallow t f) where
  {-# INLINE fmap #-}
  fmap = Rename

{-# INLINE liftFMapFS #-}
liftFMapFS :: (x -> y) -> f x -> FreeSwallow t f y
liftFMapFS h = fmap h . liftFS
{-# INLINE lowerFMapFS #-}
lowerFMapFS :: (Functor f, CanSwallow t f, Monad t) => (x -> y) -> FreeSwallow t f x -> f y
lowerFMapFS h (Unsubstituted fx) = h <$> fx
lowerFMapFS h (Substitute g sfx) = lowerSubstituteFS (fmap h . g) sfx
lowerFMapFS h (Rename g sfx) = lowerFMapFS (h . g) sfx

instance CanSwallow t (FreeSwallow t f) where
  {-# INLINE substitute #-}
  substitute = Substitute

{-| This assumes that
    prop> fold (swallow ftv) = fold (fold <$> ftv)
-}
instance (Foldable t, Foldable f) => Foldable (FreeSwallow t f) where
  {-# INLINE foldMap #-}
  foldMap h (Unsubstituted fv) = foldMap h fv
  foldMap (h :: w -> a) (Substitute (g :: v -> t w) (sfv :: FreeSwallow t f v)) =
    foldMap (foldMap h . g) sfv
  foldMap (h :: w -> a) (Rename (g :: v -> w) (sfv :: FreeSwallow t f v)) =
    foldMap (h . g) sfv

instance (Traversable t, Traversable f) => Traversable (FreeSwallow t f) where
  {-# INLINE traverse #-}
  traverse (h :: _ -> m _) sfv = uncoy $ aux h sfv
    where aux :: forall u w . (w -> m u) -> FreeSwallow t f w -> Coyoneda m (FreeSwallow t f u)
          aux h (Unsubstituted fw) = Unsubstituted <$> coy (traverse h fw)
          aux h (Substitute (g :: v -> t w) sfv) = Substitute id <$>
            (aux (traverse h . g :: v -> m (t u)) :: FreeSwallow t f v -> Coyoneda m (FreeSwallow t f (t u))) sfv
          aux (h :: w -> m u) (Rename (g :: v -> w) sfv) = aux (h . g) sfv
    
{-# INLINE liftTraverseFS #-}
liftTraverseFS :: (Applicative m, Traversable f, Traversable t) =>
  (v -> m u) -> f v -> m (FreeSwallow t f u)
liftTraverseFS h fv = Unsubstituted <$> traverse h fv
{-# INLINE lowerTraverseFS #-}
lowerTraverseFS :: (Applicative m, Traversable t, Monad t, Traversable f, CanSwallow t f) =>
  (v -> m u) -> FreeSwallow t f v -> m (f u)
lowerTraverseFS h sfv = lowerFS <$> traverse h sfv

{-# INLINE hoistFS #-}
hoistFS :: (Functor f, Functor g) => (forall x . f x -> g x) -> (FreeSwallow t f a -> FreeSwallow t g a)
hoistFS h (Unsubstituted fa) = Unsubstituted $ h fa
hoistFS h (Substitute g sfa) = Substitute g $ hoistFS h sfa
hoistFS h (Rename g sfa) = Rename g $ hoistFS h sfa
{-# INLINE liftHoistFS #-}
liftHoistFS :: (forall x . f x -> g x) -> (forall x . f x -> FreeSwallow t g x)
liftHoistFS h = liftFS . h
{-# INLINE lowerHoistFS #-}
lowerHoistFS :: (CanSwallow t f, Monad t) => (forall x . f x -> g x) -> (forall x . FreeSwallow t f x -> g x)
lowerHoistFS h = h . lowerFS

{-# INLINE hoistFSLens #-}
hoistFSLens :: forall m t f g a . (Functor m, Functor f, Functor g) =>
  (forall x . f x -> m (g x)) ->
  FreeSwallow t f a ->
  m (FreeSwallow t g a)
hoistFSLens h = uncoy . aux
  where aux :: forall x . FreeSwallow t f x -> Coyoneda m (FreeSwallow t g x)
        aux (Unsubstituted fa) = Coyoneda Unsubstituted $ h fa
        aux (Substitute g sfa) = Substitute g <$> aux sfa
        aux (Rename g sfa) = Rename g <$> aux sfa

{-# INLINE cutFS #-}
cutFS :: (CanSwallow t f, Monad t) => (forall x . f x -> g x) -> (FreeSwallow t f a -> FreeSwallow t g a)
cutFS h = liftFS . h . lowerFS
{-# INLINE cutFSLens #-}
cutFSLens :: (Functor m, CanSwallow t f, Monad t) =>
  (f a -> m (g a)) ->
  (FreeSwallow t f a -> m (FreeSwallow t g a))
cutFSLens h = fmap liftFS . h . lowerFS

{-# INLINE popFS #-}
popFS :: forall t g f x . (Functor f, Functor g) => FreeSwallow t (Compose g f) x -> Compose g (FreeSwallow t f) x
popFS = Compose . uncoy . aux
  where aux :: forall y . FreeSwallow t (Compose g f) y -> Coyoneda g ((FreeSwallow t f) y)
        aux (Unsubstituted (Compose gfx)) = coy $ Unsubstituted <$> gfx
        aux (Substitute h scgfx) = Substitute h <$> aux scgfx
        aux (Rename h scgfx) = Rename h <$> aux scgfx

{-# INLINE copopFS #-}
copopFS :: forall t g f x . (Applicative t, Traversable f, Functor g) =>
  FreeSwallow t (g :.: f) x -> ((FreeSwallow t g) :.: f) x  
copopFS (Unsubstituted (Comp1 gfx)) = Comp1 $ Unsubstituted $ gfx
copopFS (Substitute h scgfx) = Comp1 $ Substitute (traverse h) $ unComp1 $ copopFS scgfx
copopFS (Rename h scgfx) = Comp1 $ Rename (fmap h) $ unComp1 $ copopFS scgfx

-- | It is atypical to need this function.
{-# INLINE copopFS' #-}
copopFS' :: forall t g f x . (Applicative t, Traversable f, Functor g) =>
  FreeSwallow t (Compose g f) x -> (Compose (FreeSwallow t g) f) x
copopFS' (Unsubstituted (Compose gfx)) = Compose $ Unsubstituted $ gfx
copopFS' (Substitute h scgfx) = Compose $ Substitute (traverse h) $ getCompose $ copopFS' scgfx
copopFS' (Rename h scgfx) = Compose $ Rename (fmap h) $ getCompose $ copopFS' scgfx

pattern FS :: forall t f x . (CanSwallow t f, Monad t) => () => f x -> FreeSwallow t f x
pattern FS x <- (lowerFS -> x)
  where FS x = liftFS x
{-# COMPLETE FS #-}

instance NFData_ f => NFData_ (FreeSwallow t f) where
  rnf_ (Unsubstituted fa) = rnf_ fa
  rnf_ (Substitute h sfa) = rwhnf h `seq` rnf_ sfa
  rnf_ (Rename h sfa) = rwhnf h `seq` rnf_ sfa
