{-# LANGUAGE KindSignatures
           , FlexibleContexts
           , TypeOperators
           , RankNTypes
           #-}
module Generics.MultiRec.GMap where

import Generics.MultiRec.BaseF

class GMap (f :: ((* -> *) -> *) -> (* -> (* -> *) -> *) -> * -> (* -> *) -> *) where
    gmap' :: s ix -> (forall ix. Ix s ix => s ix -> r e ix -> r e' ix) -> (e -> e') -> f s r e ix -> f s r e' ix

instance GMap (I xi) where
    gmap' ix g f (I xi) = I (g index xi)

instance GMap E where
    gmap' _ _ f (E e) = E (f e)

instance GMap (K x) where
    gmap' _ _ _ (K x) = K x

instance (GMap f, GMap g) => GMap (f :+: g) where
    gmap' ix g f (L x) = L (gmap' ix g f x)
    gmap' ix g f (R x) = R (gmap' ix g f x)

instance (GMap f, GMap g) => GMap (f :*: g) where
    gmap' ix g f (x :*: y) = (gmap' ix g f x) :*: (gmap' ix g f y)

instance (GMap f) => GMap (f :>: t) where
    gmap' ix g f (Tag x) = Tag (gmap' ix g f x)

gmap :: (Ix s ix, GMap (PF s)) => s ix -> (a -> b) -> ix a -> ix b
gmap ix f x = to $ gmap' ix (\ix (I0 r) -> I0 $ gmap ix f r) f $ from x
