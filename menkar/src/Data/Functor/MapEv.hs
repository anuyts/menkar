module Data.Functor.MapEv where

(<%>) :: Functor f => f (a -> b) -> a -> f b
fh <%> a = fmap ($ a) fh
