{-# LANGUAGE TypeOperators 
           , GADTs
           , KindSignatures
           , TypeFamilies
           , MultiParamTypeClasses
           , RankNTypes
           , FlexibleContexts
           , EmptyDataDecls
           #-}
module Simple where

import Data.Char (ord)

data K a       (es :: * -> * -> *) (r :: *) = K a
data E a       (es :: * -> * -> *) (r :: *) where
    E :: (es a e) -> e -> E a es r
data I         (es :: * -> * -> *) (r :: *) where
    I :: (EIx es r) => r -> I es r
data (f :*: g) (es :: * -> * -> *) (r :: *) = f es r :*: g es r
data (f :+: g) (es :: * -> * -> *) (r :: *) = L (f es r) | R (g es r)

infixr 7 :*:
infixr 6 :+:

data Zero
data Suc a

data ParamS1 :: * -> * -> * -> * where
    Param :: ParamS1 a Zero a

data ParamS2 :: * -> * -> * -> * -> * where
    Param1 :: ParamS2 a b Zero       a
    Param2 :: ParamS2 a b (Suc Zero) b

type family PF a :: (* -> * -> *) -> * -> *

class EIx es a where
    from :: a -> PF a es a
    to :: PF a es a -> a

class GMap (f :: (* -> * -> *) -> * -> *) where
    -- Dit werkt niet, want de laatste index van 'f' (de pattern functor) kan niet veranderen, en dus ook de parameters niet.
    gmap' :: (EIx es a, EIx es2 b) => (forall n. E n es a -> E n es2 b) -> (a -> b) -> f es a -> f es2 b

instance GMap (K a) where
    gmap' _ _ (K a) = K a

instance GMap (E n) where
    gmap' f _ (E ix a) = f (E ix a)

instance GMap I where
    gmap' _ g (I r) = I (g r) -- I (to $ gmap' f $ from r)

instance (GMap f, GMap g) => GMap (f :+: g) where
    gmap' f g (L x) = L (gmap' f g x)
    gmap' f g (R y) = R (gmap' f g y)

instance (GMap f, GMap g) => GMap (f :*: g) where
    gmap' f g (x :*: y) = gmap' f g x :*: gmap' f g y

gmap :: (EIx es a, EIx es2 b, GMap (PF a), PF a ~ PF b) => (forall n. E n es a -> E n es2 b) -> a -> b
gmap f = to . gmap' f (gmap f) . from

-- Two datatypes (list and tree) to test with, with 1 and 2 type
-- parameters.
type instance (PF [a]) = K () :+: E Zero :*: I

fromList [] = L (K ())
fromList (x : xs) = R (E Param x :*: I xs)
toList :: PF [a] (ParamS1 a) [a] -> [a]
toList (L (K ())) = []
toList (R (E Param x :*: I xs)) = x : xs

instance EIx (ParamS1 a) [a] where
    from = fromList
    to = toList

f3 :: E n (ParamS1 Char) [Char] -> E n (ParamS1 Int) [Int]
f3 (E Param c) = E Param (ord c)

listTest = gmap f3 "test"

data Tree a b = Leaf a | Branch (Tree a b) b (Tree a b) deriving Show

type instance (PF (Tree a b)) = E Zero :+: I :*: E (Suc Zero) :*: I

fromTree (Leaf a) = L (E Param1 a)
fromTree (Branch l b r) = R (I l :*: E Param2 b :*: I r)
toTree :: PF (Tree a b) (ParamS2 a b) (Tree a b) -> Tree a b
toTree (L (E Param1 a)) = Leaf a
toTree (R (I l :*: E Param2 b :*: I r)) = Branch l b r

instance EIx (ParamS2 a b) (Tree a b) where
    from = fromTree
    to = toTree

testTree = Branch (Leaf 'a') True (Branch (Leaf 'b') False (Leaf 'c'))

f2 :: E n (ParamS2 Char Bool) (Tree Char Bool) -> E n (ParamS2 Int String) (Tree Int String)
f2 (E Param1 c) = E Param1 (ord c)
f2 (E Param2 b) = E Param2 (if b then "yes" else "no")

treeTest = gmap f2 testTree

-- Dit werkt niet meer, vanwege het eerste type-argument van E.
{-
f3 :: E n (ParamS2 Char Bool) (Tree Char Bool) -> E n (ParamS2 String Int) (Tree String Int)
f3 (E Param1 c) = E Param2 (ord c)
f3 (E Param2 b) = E Param1 (if b then "yes" else "no")

treeTestFail = gmap f3 testTree
-}
