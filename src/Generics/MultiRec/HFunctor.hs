{-# LANGUAGE GADTs         #-}
{-# LANGUAGE RankNTypes    #-}
{-# LANGUAGE TypeOperators #-}

-----------------------------------------------------------------------------
-- |
-- Module      :  Generics.MultiRec.HFunctor
-- Copyright   :  (c) 2008--2009 Universiteit Utrecht
-- License     :  BSD3
--
-- Maintainer  :  generics@haskell.org
-- Stability   :  experimental
-- Portability :  non-portable
--
-- The definition of functorial map.
--
-----------------------------------------------------------------------------
module Generics.MultiRec.HFunctor where

import Control.Monad (liftM, liftM2)
import Control.Applicative (Applicative(..), liftA, liftA2, WrappedMonad(..))

import Generics.MultiRec.Base

-- * Generic map

-- We define a general 'hmapA' that works on applicative functors.
-- The simpler 'hmap' is a special case.

class HFunctor f where
  hmapA :: (Applicative a) =>
           (forall ix. Ix s ix => s ix -> r ix -> a (r' ix)) ->
           f s r ix -> a (f s r' ix)

instance HFunctor (I xi) where
  hmapA f (I x) = liftA I (f index x)

instance HFunctor (K x) where
  hmapA _ (K x)  = pure (K x)

instance HFunctor U where
  hmapA _ U = pure U

instance (HFunctor f, HFunctor g) => HFunctor (f :+: g) where
  hmapA f (L x) = liftA L (hmapA f x)
  hmapA f (R y) = liftA R (hmapA f y)

instance (HFunctor f, HFunctor g) => HFunctor (f :*: g) where
  hmapA f (x :*: y) = liftA2 (:*:) (hmapA f x) (hmapA f y)

instance HFunctor f => HFunctor (f :>: ix) where
  hmapA f (Tag x) = liftA Tag (hmapA f x)

instance HFunctor f => HFunctor (C c f) where
  hmapA f (C x) = liftA C (hmapA f x)

-- | The function 'hmap' takes a functor @f@. All the recursive instances
-- in that functor are wrapped by an application of @r@. The argument to
-- 'hmap' takes a function that transformes @r@ occurrences into @r'@
-- occurrences, for every @ix@. In order to associate the index @ix@
-- with the correct system @s@, the argument to @hmap@ is additionally
-- parameterized by a witness of type @s ix@. 
hmap  :: (HFunctor f) =>
         (forall ix. Ix s ix => s ix -> r ix -> r' ix) ->
         f s r ix -> f s r' ix
hmap f x = unI0 (hmapA (\ ix x -> I0 (f ix x)) x)

-- | Monadic version of 'hmap'.
hmapM :: (HFunctor f, Monad m) =>
         (forall ix. Ix s ix => s ix -> r ix -> m (r' ix)) ->
         f s r ix -> m (f s r' ix)
hmapM f x = unwrapMonad (hmapA (\ ix x -> WrapMonad (f ix x)) x)
