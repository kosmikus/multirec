{-# LANGUAGE GADTs
           , KindSignatures
           , MultiParamTypeClasses
           , TypeFamilies
           , TypeOperators
           #-}
module BinTreeRepsF where

import Generics.MultiRec.BaseF
import BinTreeDatatype

data BinTreeU :: (* -> *) -> * where
    BinTree :: BinTreeU BinTree

type instance PF BinTreeU = E :>: BinTree :+:
                            (I BinTree :*: I BinTree) :>: BinTree

instance Ix BinTreeU BinTree where
    from_ (Leaf x)  = L (Tag (E x))
    from_ (Bin l r) = R (Tag (I (I0 l) :*: I (I0 r)))
    to_ (L (Tag (E x))) = Leaf x
    to_ (R (Tag (I (I0 l) :*: I (I0 r)))) = Bin l r
    index = BinTree
