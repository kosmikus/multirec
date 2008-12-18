{-# LANGUAGE GADTs
           , KindSignatures
           , MultiParamTypeClasses
           , TypeFamilies
           , TypeOperators
           #-}
module TreeReps where

import Generics.MultiRec
import TreeDatatype

data WTreeU :: * -> * -> * -> * where
    WTree :: WTreeU a w (WTree a w)

type instance PF (WTreeU a w) = K a :>: WTree a w
                            :+: (I (WTree a w) :*: I (WTree a w)) :>: WTree a w
                            :+: (I (WTree a w) :*: K w) :>: WTree a w

instance Ix (WTreeU a w) (WTree a w) where
    from_ (Leaf x) = L (Tag (K x))
    from_ (Fork l r) = R (L (Tag (I (I0 l) :*: I (I0 r))))
    from_ (WithWeight t w) = R (R (Tag (I (I0 t) :*: K w)))
    to_ (L (Tag (K x))) = Leaf x
    to_ (R (L (Tag (I (I0 l) :*: I (I0 r))))) = Fork l r
    to_ (R (R (Tag (I (I0 t) :*: K w)))) = WithWeight t w
    index = WTree
