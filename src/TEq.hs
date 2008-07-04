{-# LANGUAGE GADTs          #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeOperators  #-}

module TEq where

import Base
import Void

infix 4 :=:

data (:=:) :: * -> * -> * where
  Refl :: a :=: a

cast :: a :=: b -> a -> b
cast Refl x = x