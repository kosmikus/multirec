{-# LANGUAGE KindSignatures
           , FlexibleContexts
           , TypeOperators
           , RankNTypes
           , RelaxedPolyRec
           , TypeFamilies
           , ScopedTypeVariables
           , MultiParamTypeClasses
           , FlexibleInstances
           #-}
module Generics.MultiRec.GMap where

import Control.Applicative
import Generics.MultiRec.Base
import Generics.MultiRec.Elems.One
import Data.Char

class GMap (f :: ((* -> *) -> * -> *) -> (* -> *) -> (* -> *) -> * -> *) s es2 where
    -- Omdat f hier iets is als (PF (ListU (Elems Char))), kan je de
    -- element-types niet veranderen...
    gmap' :: s es ix -> s es2 ix' -> (forall ix. (Ix s es ix, Ix s es2 ix) => s es ix -> s es2 ix -> r ix -> r ix) -> (forall n. es n -> es2 n) -> f s es r ix -> f s es2 r ix'

instance GMap U s es where
    gmap' _ _ _ _ U = U

instance GMap (K x) s es where
    gmap' _ _ _ _ (K x) = K x

instance GMap (E n) s es where
    gmap' _ _ _ f (E n) = E (f n)

instance Ix s es xi => GMap (I xi) s es where
    gmap' _ _ g _ (I x) = I (g index index x)

instance (GMap f s es, GMap g s es) => GMap (f :+: g) s es where
    gmap' ix ix' g f (L x) = L (gmap' ix ix' g f x)
    gmap' ix ix' g f (R x) = R (gmap' ix ix' g f x)

instance (GMap f s es, GMap g s es) => GMap (f :*: g) s es where
    gmap' ix ix' g f (x :*: y) = (gmap' ix ix' g f x) :*: (gmap' ix ix' g f y)

instance (GMap f s es2, Eq_ (s es2), Ix s es2 t) => GMap (f :>: t) s es2 where
    gmap' ix ix' g f (Tag x) = case eq_ ix' (index :: s es2 t) of
        Nothing   -> error "The impossible happened!"
        Just Refl -> Tag (gmap' ix ix' g f x)

gmap :: (Ix s es ix, Ix s es2 ix', GMap (PF (s es2)) s es2, PF (s es) ~ PF (s es2)) => s es ix -> s es2 ix' -> (forall n. es n -> es2 n) -> ix -> ix'
gmap ix ix' f = to . gmap' ix ix' (\ix ix' (I0 x) -> I0 (gmap ix ix' f x)) f . from

{-
class GMap f where
    gmapA' :: (Applicative a) => s es ix -> (forall ix. (Ix s es ix, Ix s es2 ix) => s es ix -> r ix -> a (r' ix')) -> (forall n. es n -> a (es2 n)) -> f s es r ix -> a (f s es2 r' ix')

instance GMap (I xi) where
    -- Ik mag hier geen I gebruiken aan de rechterkant, omdat ik niet
    -- Ix s es2 ix in de context heb, alleen Ix s es ix (door pattern
    -- match op I).
    gmapA' ix g f (I xi) = undefined -- I <$> (g index xi)

instance GMap U where
    gmapA' _ _ _ U = pure U

instance GMap (E n) where
    gmapA' _ _ f (E e) = E <$> (f e)

instance GMap (K x) where
    gmapA' _ _ _ (K x) = pure $ K x

instance (GMap f, GMap g) => GMap (f :+: g) where
    gmapA' ix g f (L x) = L <$> (gmapA' ix g f x)
    gmapA' ix g f (R x) = R <$> (gmapA' ix g f x)

instance (GMap f, GMap g) => GMap (f :*: g) where
    gmapA' ix g f (x :*: y) = (:*:) <$> (gmapA' ix g f x) <*> (gmapA' ix g f y)

instance (GMap f) => GMap (f :>: t) where
    gmapA' ix g f (Tag x) = Tag <$> (gmapA' ix g f x)

gmapAF :: (GMap (PF (s es)), GMap g, Applicative a, PF (s es) ~ PF (s es2)) => s es ix -> (forall n. es n -> a (es2 n)) -> g s es I0 ix -> a (g s es2 I0 ix)
gmapAF ix f = undefined --gmapA' ix (\ix (I0 r) -> I0 <$> gmapA ix f r) f

gmapA :: (Ix s es ix, Ix s es2 ix, GMap (PF (s es)), Applicative a, PF (s es) ~ PF (s es2)) => s es ix -> (forall n. es n -> a (es2 n)) -> ix -> a ix
gmapA ix f x = to <$> (gmapAF ix f $ from x)

gmap :: (Ix s es ix, Ix s es2 ix, GMap (PF (s es)), PF (s es) ~ PF (s es2)) => s es ix -> (forall n. es n -> es2 n) -> ix -> ix'
gmap ix f = undefined --to . unI0 . gmapA' ix undefined (I0 . f) . from --to . unI0 . gmapA' ix (\ix r -> I0 $ undefined {-gmap ix f r-}) (I0 . f) . from
-- hmap f x = unI0 (hmapA (\ ix x -> I0 (f ix x)) x)
-}
