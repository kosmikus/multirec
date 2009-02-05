{-# LANGUAGE GADTs
           , KindSignatures
           , TypeFamilies
           , FlexibleContexts
           #-}
module MultiParam.Two (module MultiParam, Elems(E0, E1), bimap) where

import MultiParam

data Elems :: * -> * -> * -> * where
    E0 :: a -> Elems a b Zero
    E1 :: b -> Elems a b (Suc Zero)

mapElems :: (a -> c) -> (b -> d) -> Elems a b n -> Elems c d n
mapElems f g (E0 a) = E0 (f a)
mapElems f g (E1 b) = E1 (g b)

bimap :: (EIx (Elems a b) (f a b), EIx (Elems c d) (f c d), GMap (PF (f a b)), PF (f a b) ~ PF (f c d)) => (a -> c) -> (b -> d) -> f a b -> f c d
bimap f g = gmap (mapElems f g)
