{-# LANGUAGE GADTs
           , KindSignatures
           , MultiParamTypeClasses
           , TypeFamilies
           , TypeOperators
           #-}
module ListRep where

import Generics.MultiRec

data ListU :: * -> * -> * where
    List :: ListU a [a]

type instance PF (ListU a) = U :>: [a]
                         :+: (K a :*: I ([a])) :>: [a]

instance Ix (ListU a) [a] where
    from_ [] = L (Tag U)
    from_ (x : xs) = R (Tag (K x :*: I (I0 xs)))
    to_ (L (Tag U)) = []
    to_ (R (Tag (K x :*: I (I0 xs)))) = x : xs
    index = List

instance Eq_ (ListU a) where
    eq_ List List = Just Refl
