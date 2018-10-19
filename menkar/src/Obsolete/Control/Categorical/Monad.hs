module Control.Categorical.Monad where

import qualified Prelude as P
import Prelude (($))
import Control.Category
import Control.Categorical.Functor

class (Endofunctor m hom) => Monad (m :: kobj -> kobj) (hom :: kobj -> kobj -> *) where
  return :: hom a (m a)
  bind :: hom a (m b) -> hom (m a) (m b)

------------------------

{-| Natural transformations from 'f' to 'g' with codomain category 'cod'
-}
newtype NT cod f g = NT {runNT :: (forall a . cod (f a) (g a))}

{-| If 'cod' is a category, then functors to 'cod' constitute the category 'NT cod'
-}
instance Category cod => Category (NT cod) where
  id = NT id
  NT nu . NT mu = NT (nu . mu)

{-| If @dom@ is a kind and 'cod' is a category, then @NT cod f@ is a functor @(dom -> cod) -> *@.
-}
instance Category cod => Functor (NT cod f) (NT cod) (->) where
  fmap (NT nu) (NT mu) = NT (nu . mu)

------------------------

return1 :: (Monad m (NT (->))) => a x -> m a x
return1 = runNT return
(>>=!) :: (Monad m (NT (->))) => m a x -> (forall y . a y -> m b y) -> m b x
ma >>=! f = runNT (bind $ NT f) ma
(>>!) :: (Monad m (NT (->))) => m a x -> (forall y . m b y) -> m b x
ma >>! mb = ma >>=! \_ -> mb
