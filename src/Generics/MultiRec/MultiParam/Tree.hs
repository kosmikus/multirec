{-# LANGUAGE TypeOperators
           , TypeFamilies
           , MultiParamTypeClasses
           #-}
module MultiParam.Tree where

import MultiParam.Two
import Data.Char (ord)

data Tree a b = Leaf a | Branch (Tree a b) b (Tree a b) deriving Show

type instance (PF (Tree a b)) = E Zero :+: I :*: E (Suc Zero) :*: I

fromTree (Leaf a) = L (E (E0 a))
fromTree (Branch l b r) = R (I l :*: E (E1 b) :*: I r)
toTree :: PF (Tree a b) (Elems a b) (Tree a b) -> Tree a b
toTree (L (E (E0 a))) = Leaf a
toTree (R (I l :*: E (E1 b) :*: I r)) = Branch l b r

instance EIx (Elems a b) (Tree a b) where
    from = fromTree
    to = toTree

testTree :: Tree Char Bool
testTree = Branch (Leaf 'a') True (Branch (Leaf 'b') False (Leaf 'c'))

f2 :: Elems Char Bool n -> Elems Int String n
f2 (E0 c) = E0 (ord c)
f2 (E1 b) = E1 (if b then "yes" else "no")

treeTest :: Tree Int String
treeTest = gmap f2 testTree

-- Dit werkt niet, vanwege het laatste type-argument van ParamS2.
{-
f4 :: Elems Char Bool n -> Elems String Int n
f4 (E0 c) = E1 (ord c)
f4 (E1 b) = E0 (if b then "yes" else "no")

treeTestFail :: Tree String Int
treeTestFail = gmap f4 testTree
-}

