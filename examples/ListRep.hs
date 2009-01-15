{-# LANGUAGE GADTs
           , TypeFamilies
           , TypeOperators
           , KindSignatures
           , MultiParamTypeClasses
           #-}

module ListRep where

import qualified Generics.MultiRec.Base as Base
import Generics.MultiRec.BaseF

data ListU :: (* -> *) -> * where
    List :: ListU []

type instance PF ListU = K () :>: []
                     :+: E :*: I [] :>: []

instance Ix ListU [] where
    from_ [] = L (Tag (K ()))
    from_ (x : xs) = R (Tag (E x :*: I (I0F xs)))
    to_ (L (Tag (K ()))) = []
    to_ (R (Tag (E x :*: I (I0F xs)))) = x : xs
    index = List

type ListOf = Base.Comp (I []) ListU []
type ListOfF = Comp (I []) ListU []
