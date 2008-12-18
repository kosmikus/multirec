{-# LANGUAGE GADTs
           , KindSignatures
           , MultiParamTypeClasses
           , TypeFamilies
           , TypeOperators
           #-}
module ListRepF where

import Generics.MultiRec.BaseF

data ListU :: (* -> *) -> * where
    List :: ListU []

type instance PF (ListU) = K () :>: []
                         :+: (E :*: I []) :>: []

instance Ix ListU [] where
    from_ [] = L (Tag (K ()))
    from_ (x : xs) = R (Tag (E x :*: I (I0 xs)))
    to_ (L (Tag (K ()))) = []
    to_ (R (Tag (E x :*: I (I0 xs)))) = x : xs
    index = List
