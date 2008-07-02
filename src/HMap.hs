{-# LANGUAGE GADTs         #-}
{-# LANGUAGE RankNTypes    #-}
{-# LANGUAGE TypeOperators #-}

module HMap where

import Base

-------------------------------------------------------------------------------
-- generic map
-------------------------------------------------------------------------------

class HMap f where
  hmap :: (forall ix. Ix l ix => l ix -> ix -> ix) -> f l ix -> f l ix

instance HMap (Id xi) where hmap f (Id xi x) = Id xi (f xi x)

instance HMap (K x)   where hmap _ (K x)  = K x

instance (HMap f, HMap g) => HMap (f :+: g) where
  hmap f (L x) = L (hmap f x)
  hmap f (R y) = R (hmap f y)

instance (HMap f, HMap g) => HMap (f :*: g) where
  hmap f (x :*: y) = hmap f x :*: hmap f y

instance HMap f => HMap (f ::: ix) where
  hmap f (Tag x) = Tag (hmap f x)