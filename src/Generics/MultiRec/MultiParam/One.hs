{-# LANGUAGE GADTs
           , KindSignatures
           #-}
module MultiParam.One (module MultiParam, Elems(E0)) where

import MultiParam

data Elems :: * -> * -> * where
    E0 :: a -> Elems a Zero
