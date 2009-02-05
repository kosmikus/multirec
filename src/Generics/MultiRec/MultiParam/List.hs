{-# LANGUAGE TypeOperators
           , TypeFamilies
           , MultiParamTypeClasses
           #-}
module MultiParam.List where

import Prelude hiding (map)
import MultiParam.One
import Data.Char (ord)

type instance (PF [a]) = K () :+: E Zero :*: I

fromList [] = L (K ())
fromList (x : xs) = R (E (E0 x) :*: I xs)
toList :: PF [a] (Elems a) [a] -> [a]
toList (L (K ())) = []
toList (R (E (E0 x) :*: I xs)) = x : xs

instance EIx (Elems a) [a] where
    from = fromList
    to = toList

f3 :: Elems Char n -> Elems Int n
f3 (E0 c) = E0 (ord c)

listTest :: [Int] -- Needs a type signature due to the monomorphism restriction
listTest = gmap f3 "test"

-- we can also use the specialized map for one element data types:
listTest' = map ord "test"
