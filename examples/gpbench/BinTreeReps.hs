{-# LANGUAGE GADTs
           , KindSignatures
           , MultiParamTypeClasses
           , TypeFamilies
           , TypeOperators
           #-}
module BinTreeReps where

import Generics.MultiRec
import BinTreeDatatype

data BinTreeU :: * -> * -> * where
    BinTree :: BinTreeU a (BinTree a)

type instance PF (BinTreeU a) = K a :>: BinTree a :+:
                                (I (BinTree a) :*: I (BinTree a)) :>: (BinTree a)

instance Ix (BinTreeU a) (BinTree a) where
    from_ (Leaf x)  = L (Tag (K x))
    from_ (Bin l r) = R (Tag (I (I0 l) :*: I (I0 r)))
    to_ (L (Tag (K x))) = Leaf x
    to_ (R (Tag (I (I0 l) :*: I (I0 r)))) = Bin l r
    index = BinTree

instance Eq_ (BinTreeU a) where
    eq_ BinTree BinTree = Just Refl
