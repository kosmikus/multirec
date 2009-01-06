{-# LANGUAGE TypeOperators 
           , GADTs
           , KindSignatures
           , TypeFamilies
           , MultiParamTypeClasses
           , ExistentialQuantification
           , RankNTypes
           , FlexibleContexts
           #-}
module Simple where

import Data.Char (ord)

-- The datatype I want to model as an example of a datatype with more than one type param
data Tree a b = Leaf a | Branch (Tree a b) b (Tree a b) deriving Show

data K a (es :: * -> *) (r :: *) = K a
data E (es :: * -> *) (r :: *) = forall e. E (es e) e
data I (es :: * -> *) (r :: *) where
    I :: (EIx es r) => r -> I es r
data (f :*: g) (es :: * -> *) (r :: *) = f es r :*: g es r
data (f :+: g) (es :: * -> *) (r :: *) = L (f es r) | R (g es r)

infixr 7 :*:
infixr 6 :+:

data ParamS2 :: * -> * -> * -> * where
    Param1 :: ParamS2 a b a
    Param2 :: ParamS2 a b b

type family PF a :: (* -> *) -> * -> *

class EIx es a where
    from :: a -> PF a es a
    to :: PF a es a -> a

type instance (PF (Tree a b)) = E :+: I :*: E :*: I

instance EIx (ParamS2 a b) (Tree a b) where
    from = fromTree
    to = toTree

class GMap (f :: (* -> *) -> * -> *) where
    -- Dit werkt niet, want de laatste index van 'f' (de pattern functor) kan niet veranderen, en dus ook de parameters niet.
    gmap :: (EIx es a, EIx es2 b) => (E es a -> E es2 b) -> (a -> b) -> f es a -> f es2 b
--    gmap :: (EIx es a, EIx es2 a) => (forall a b. es a -> a -> (es2 b, b)) -> f es a -> f es2 a

instance GMap (K a) where
    gmap _ _ (K a) = K a

instance GMap E where
    gmap f _ (E ix a) = f (E ix a)

instance GMap I where
    gmap _ g (I r) = I (g r) -- I (to $ gmap f $ from r)

instance (GMap f, GMap g) => GMap (f :+: g) where
    gmap f g (L x) = L (gmap f g x)
    gmap f g (R y) = R (gmap f g y)

instance (GMap f, GMap g) => GMap (f :*: g) where
    gmap f g (x :*: y) = gmap f g x :*: gmap f g y

fromTree (Leaf a) = L (E Param1 a)
fromTree (Branch l b r) = R (I l :*: E Param2 b :*: I r)
toTree :: PF (Tree a b) (ParamS2 a b) (Tree a b) -> Tree a b
toTree (L (E Param1 a)) = Leaf a
toTree (R (I l :*: E Param2 b :*: I r)) = Branch l b r

{-
f :: ParamS2 Char Bool c -> c -> (ParamS2 Char Bool c, c)
f Param1 c = (Param1, ord c)
f Param2 b = (Param2, if b then "yes" else "no")
-}

testTree = Branch (Leaf 'a') True (Branch (Leaf 'b') False (Leaf 'c'))

f :: ParamS2 Char Bool c -> c -> E (ParamS2 Int String) r
f Param1 c = E Param1 (ord c)
f Param2 b = E Param2 (if b then "yes" else "no")

f2 :: E (ParamS2 Char Bool) (Tree Char Bool) -> E (ParamS2 Int String) (Tree Int String)
f2 (E Param1 c) = E Param1 (ord c)
f2 (E Param2 b) = E Param2 (if b then "yes" else "no")

res = toTree $ gmap f2 g $ fromTree testTree
  where
    g = toTree . gmap f2 g . fromTree

-- Dit werkt, maar is niet type-safe: onderstaande functie res2 crasht
f3 :: E (ParamS2 Char Bool) (Tree Char Bool) -> E (ParamS2 String Int) (Tree String Int)
f3 (E Param1 c) = E Param2 (ord c)
f3 (E Param2 b) = E Param1 (if b then "yes" else "no")

res2 = toTree $ gmap f3 g $ fromTree testTree
  where
    g = toTree . gmap f3 g . fromTree
