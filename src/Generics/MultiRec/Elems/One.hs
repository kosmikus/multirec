{-# LANGUAGE GADTs
           , KindSignatures
           #-}
module Generics.MultiRec.Elems.One (module Generics.MultiRec.Base, Elems(..)) where

import Generics.MultiRec.Base

data Elems :: * -> * -> * where
    E0 :: a -> Elems a Zero
