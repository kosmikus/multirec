{-# LANGUAGE KindSignatures
           , FlexibleContexts
           , TypeOperators
           , RankNTypes
           , RelaxedPolyRec
           #-}
module Generics.MultiRec.GZipWith where

import Generics.MultiRec.BaseF

class GZipWith f where
    gzipWith' :: s ix -> (forall ix. Ix s ix => s ix -> r e1 ix -> r e2 ix -> r e3 ix) -> (e1 -> e2 -> e3) -> f s r e1 ix -> f s r e2 ix -> f s r e3 ix

instance GZipWith (I xi) where
    gzipWith' ix g f (I xi) (I xi2) = I $ g index xi xi2

instance GZipWith E where
    gzipWith' ix g f (E e) (E e2) = E $ f e e2

instance (GZipWith f, GZipWith g, Ix s' ix', GZipWith (PF s')) => GZipWith (Comp f s' ix' g) where
    gzipWith' ix g f (Comp x1) (Comp x2) = Comp $ gzipWithF index (gzipWith' ix g f) x1 x2

instance Eq x => GZipWith (K x) where
    gzipWith' ix g f (K x) (K x2) | x == x2   = K x
                                  | otherwise = K $ error "Constant elements not equal in GZipWith."

instance (GZipWith f, GZipWith g) => GZipWith (f :+: g) where
    gzipWith' ix g f (L x) (L x2) = L $ gzipWith' ix g f x x2
    gzipWith' ix g f (R x) (R x2) = R $ gzipWith' ix g f x x2

instance (GZipWith f, GZipWith g) => GZipWith (f :*: g) where
    gzipWith' ix g f (x :*: y) (x2 :*: y2) = gzipWith' ix g f x x2 :*: gzipWith' ix g f y y2

instance (GZipWith f) => GZipWith (f :>: t) where
    gzipWith' ix g f (Tag x) (Tag x2) = Tag $ gzipWith' ix g f x x2

gzipWithF :: (GZipWith f, GZipWith (PF s)) => s ix -> (a -> b -> c) -> f s I0F a ix -> f s I0F b ix -> f s I0F c ix
gzipWithF ix f a b = gzipWith' ix (\ix (I0F x) (I0F y) -> I0F $ gzipWith ix f x y) f a b

gzipWith :: (Ix s ix, GZipWith (PF s)) => s ix -> (a -> b -> c) -> ix a -> ix b -> ix c
gzipWith ix f a b = to $ gzipWithF ix f (from a) (from b)
