{-# LANGUAGE GADTs
           , KindSignatures
           #-}
module MultiParam.Two (module MultiParam, Elems(E0, E1)) where

import MultiParam

data Elems :: * -> * -> * -> * where
    E0 :: a -> Elems a b Zero
    E1 :: b -> Elems a b (Suc Zero)

