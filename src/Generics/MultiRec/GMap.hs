{-# LANGUAGE KindSignatures
           , FlexibleContexts
           , TypeOperators
           , RankNTypes
           , RelaxedPolyRec
           #-}
module Generics.MultiRec.GMap where

import Control.Applicative
import Generics.MultiRec.BaseF

class GMap (f :: ((* -> *) -> *) -> (* -> (* -> *) -> *) -> * -> (* -> *) -> *) where
    gmapA' :: (Applicative a) => s ix -> (forall ix. Ix s ix => s ix -> r e ix -> a (r e' ix)) -> (e -> a e') -> f s r e ix -> a (f s r e' ix)

instance GMap (I xi) where
    gmapA' ix g f (I xi) = I <$> (g index xi)

instance GMap E where
    gmapA' _ _ f (E e) = E <$> (f e)

instance (GMap f, GMap g, Ix s' ix', GMap (PF s')) => GMap (Comp f s' ix' g) where
    gmapA' ix g f (Comp x) = Comp <$> gmapAF index (gmapA' ix g f) x

instance GMap (K x) where
    gmapA' _ _ _ (K x) = pure $ K x

instance (GMap f, GMap g) => GMap (f :+: g) where
    gmapA' ix g f (L x) = L <$> (gmapA' ix g f x)
    gmapA' ix g f (R x) = R <$> (gmapA' ix g f x)

instance (GMap f, GMap g) => GMap (f :*: g) where
    gmapA' ix g f (x :*: y) = (:*:) <$> (gmapA' ix g f x) <*> (gmapA' ix g f y)

instance (GMap f) => GMap (f :>: t) where
    gmapA' ix g f (Tag x) = Tag <$> (gmapA' ix g f x)

gmapAF :: (GMap (PF s), GMap g, Applicative f) => s ix -> (a -> f b) -> g s I0F a ix -> f (g s I0F b ix)
gmapAF ix f = gmapA' ix (\ix (I0F r) -> I0F <$> gmapA ix f r) f

gmapA :: (Ix s ix, GMap (PF s), Applicative f) => s ix -> (a -> f b) -> ix a -> f (ix b)
gmapA ix f x = to <$> (gmapAF ix f $ from x)

gmap :: (Ix s ix, GMap (PF s)) => s ix -> (a -> b) -> ix a -> ix b
gmap ix f = to . unI0 . gmapA' ix (\ix (I0F r) -> I0 $ I0F $ gmap ix f r) (I0 . f) . from
