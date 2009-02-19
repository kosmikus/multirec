{-# LANGUAGE TypeOperators 
           , KindSignatures
           , TypeFamilies
           , MultiParamTypeClasses
           , RankNTypes
           , FlexibleContexts
           , EmptyDataDecls
           #-}
module MultiParam where

data K a       (es :: * -> *) r = K a
data E a       (es :: * -> *) r = E (es a)
data I         (es :: * -> *) r = I r
data (f :*: g) (es :: * -> *) r = f es r :*: g es r
data (f :+: g) (es :: * -> *) r = L (f es r) | R (g es r)

infixr 7 :*:
infixr 6 :+:

data Zero
data Suc a

type family PF a :: (* -> *) -> * -> *

class EIx es a where
    from :: a -> PF a es a
    to :: PF a es a -> a

class GMap f where
    gmap' :: (forall n. es n -> es2 n) -> (a -> b) -> f es a -> f es2 b

instance GMap (K a) where
    gmap' _ _ (K a) = K a

instance GMap (E n) where
    gmap' f _ (E e) = E (f e)

instance GMap I where
    gmap' _ g (I r) = I (g r)

instance (GMap f, GMap g) => GMap (f :+: g) where
    gmap' f g (L x) = L (gmap' f g x)
    gmap' f g (R y) = R (gmap' f g y)

instance (GMap f, GMap g) => GMap (f :*: g) where
    gmap' f g (x :*: y) = gmap' f g x :*: gmap' f g y

gmap :: (EIx es a, EIx es2 b, GMap (PF a), PF a ~ PF b) => (forall n. es n -> es2 n) -> a -> b
gmap f = to . gmap' f (gmap f) . from
