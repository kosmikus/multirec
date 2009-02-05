{-# LANGUAGE TypeOperators 
           , GADTs
           , KindSignatures
           , TypeFamilies
           , MultiParamTypeClasses
           , RankNTypes
           , FlexibleContexts
           , EmptyDataDecls
           #-}
module MultiParam where

import Data.Char (ord)

data K a       (es :: * -> *) r = K a
data E a       (es :: * -> *) r where
    E :: es a -> E a es r
data I         (es :: * -> *) r = I r
data (f :*: g) (es :: * -> *) r = f es r :*: g es r
data (f :+: g) (es :: * -> *) r = L (f es r) | R (g es r)

infixr 7 :*:
infixr 6 :+:

data Zero
data Suc a

data ParamS1 :: * -> * -> * where
    Param :: a -> ParamS1 a Zero

data ParamS2 :: * -> * -> * -> * where
    Param1 :: a -> ParamS2 a b Zero
    Param2 :: b -> ParamS2 a b (Suc Zero)

type family PF a :: (* -> *) -> * -> *

class EIx es a where
    from :: a -> PF a es a
    to :: PF a es a -> a

class GMap (f :: (* -> *) -> * -> *) where
    gmap' :: (forall n. es n -> es2 n) -> (a -> b) -> f es a -> f es2 b

instance GMap (K a) where
    gmap' _ _ (K a) = K a

instance GMap (E n) where
    gmap' f _ (E e) = E (f e)

instance GMap I where
    gmap' _ g (I r) = I (g r) -- I (to $ gmap' f $ from r)

instance (GMap f, GMap g) => GMap (f :+: g) where
    gmap' f g (L x) = L (gmap' f g x)
    gmap' f g (R y) = R (gmap' f g y)

instance (GMap f, GMap g) => GMap (f :*: g) where
    gmap' f g (x :*: y) = gmap' f g x :*: gmap' f g y

gmap :: (EIx es a, EIx es2 b, GMap (PF a), PF a ~ PF b) => (forall n. es n -> es2 n) -> a -> b
gmap f = to . gmap' f (gmap f) . from

-- Two datatypes (list and tree) to test with, with 1 and 2 type
-- parameters.
type instance (PF [a]) = K () :+: E Zero :*: I

fromList [] = L (K ())
fromList (x : xs) = R (E (Param x) :*: I xs)
toList :: PF [a] (ParamS1 a) [a] -> [a]
toList (L (K ())) = []
toList (R (E (Param x) :*: I xs)) = x : xs

instance EIx (ParamS1 a) [a] where
    from = fromList
    to = toList

f3 :: ParamS1 Char n -> ParamS1 Int n
f3 (Param c) = Param (ord c)

listTest :: [Int] -- Needs a type signature due to the monomorphism restriction
listTest = gmap f3 "test"

data Tree a b = Leaf a | Branch (Tree a b) b (Tree a b) deriving Show

type instance (PF (Tree a b)) = E Zero :+: I :*: E (Suc Zero) :*: I

fromTree (Leaf a) = L (E (Param1 a))
fromTree (Branch l b r) = R (I l :*: E (Param2 b) :*: I r)
toTree :: PF (Tree a b) (ParamS2 a b) (Tree a b) -> Tree a b
toTree (L (E (Param1 a))) = Leaf a
toTree (R (I l :*: E (Param2 b) :*: I r)) = Branch l b r

instance EIx (ParamS2 a b) (Tree a b) where
    from = fromTree
    to = toTree

testTree :: Tree Char Bool
testTree = Branch (Leaf 'a') True (Branch (Leaf 'b') False (Leaf 'c'))

f2 :: ParamS2 Char Bool n -> ParamS2 Int String n
f2 (Param1 c) = Param1 (ord c)
f2 (Param2 b) = Param2 (if b then "yes" else "no")

treeTest :: Tree Int String
treeTest = gmap f2 testTree

-- Dit werkt niet, vanwege het laatste type-argument van ParamS2.
{-
f4 :: ParamS2 Char Bool n -> ParamS2 String Int n
f4 (Param1 c) = Param2 (ord c)
f4 (Param2 b) = Param1 (if b then "yes" else "no")

treeTestFail :: Tree String Int
treeTestFail = gmap f4 testTree
-}
