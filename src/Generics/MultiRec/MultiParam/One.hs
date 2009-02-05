{-# LANGUAGE GADTs
           , KindSignatures
           , TypeFamilies
           , FlexibleContexts
           #-}
module MultiParam.One (module MultiParam, Elems(E0), map) where

import Prelude hiding (map)
import MultiParam

data Elems :: * -> * -> * where
    E0 :: a -> Elems a Zero

mapElems :: (a -> b) -> Elems a n -> Elems b n
mapElems f (E0 a) = E0 (f a)

map :: (EIx (Elems a) (f a), EIx (Elems b) (f b), GMap (PF (f a)), PF (f a) ~ PF (f b)) => (a -> b) -> f a -> f b
map f = gmap (mapElems f)
