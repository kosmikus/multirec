{-# LANGUAGE RankNTypes
           , FlexibleContexts
           , FlexibleInstances
           , TypeOperators
           , MultiParamTypeClasses
           , GADTs
           , KindSignatures
           , TypeFamilies
           , ScopedTypeVariables
           #-}
module Generics.MultiRec.Gen where

import Generics.MultiRec

class HGen f s where -- Het 's' argument is nodig voor de context van de instance voor 'I'
    hgen :: Int -> s ix -> (forall ix. Ix s ix => s ix -> [r ix]) -> [f s r ix]

instance (Ix s xi) => HGen (I xi) s where
    hgen n ix f = map I $ f index

instance HGen (K Char) s where
    hgen 0 _ _ = []
    hgen n ix f = [K '0']

instance HGen (K [a]) s where
    hgen 0 _ _ = []
    hgen n ix f = [K []]

instance HGen (K ()) s where
    hgen 0 _ _ = []
    hgen n ix f = [K ()]

instance HGen U s where
    hgen n ix f = [U]

instance HGen (K Float) s where
    hgen 0 _ _ = []
    hgen n ix f = [K 0]

instance HGen (K Int) s where
    hgen 0 _ _ = []
    hgen n ix f = [K 0]

instance (HGen f s, HGen g s) => HGen (f :+: g) s where
    hgen n ix f = map L (hgen n ix f) ++ map R (hgen n ix f)

instance (HGen f s, HGen g s) => HGen (f :*: g) s where
    hgen n ix f = [ x :*: y | x <- hgen n ix f, y <- hgen n ix f ]

instance (Eq_ s, Ix s t, HGen f s) => HGen (f :>: t) s where
    hgen n ix f = case eq_ ix (index :: s t) of
        Nothing -> []
        Just Refl -> map Tag (hgen n ix f)

gen :: (Ix s ix, HGen (PF s) s) => Int -> s ix -> [ix]
gen 0 _  = []
gen n ix = map to $ hgen (n - 1) ix (\ix -> map I0 (gen (n - 1) ix))
