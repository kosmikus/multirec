{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances     #-}

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
import Control.Applicative (Applicative(..), (<$>), (<*>), WrappedMonad(..))

import Generics.MultiRec.Base

-- * Generic map

-- We define a general 'hmapA' that works on applicative functors.
-- The simpler 'hmap' is a special case.

class HFunctor phi f where
  hmapA :: (Applicative a) =>
           (forall ix. phi ix -> r ix -> a (r' ix)) ->
           f r ix -> a (f r' ix)

instance El phi xi => HFunctor phi (I xi) where
  hmapA f (I x) = I <$> f proof x

instance HFunctor phi (K x) where
  hmapA _ (K x) = pure (K x)

instance HFunctor phi U where
  hmapA _ U = pure U

instance (HFunctor phi f, HFunctor phi g) => HFunctor phi (f :+: g) where
  hmapA f (L x) = L <$> hmapA f x
  hmapA f (R y) = R <$> hmapA f y

instance (HFunctor phi f, HFunctor phi g) => HFunctor phi (f :*: g) where
  hmapA f (x :*: y) = (:*:) <$> hmapA f x <*> hmapA f y

instance HFunctor phi f => HFunctor phi (f :>: ix) where
  hmapA f (Tag x) = Tag <$> hmapA f x

instance (Constructor c, HFunctor phi f) => HFunctor phi (C c f) where
  hmapA f (C x) = C <$> hmapA f x

-- | The function 'hmap' takes a functor @f@. All the recursive instances
-- in that functor are wrapped by an application of @r@. The argument to
-- 'hmap' takes a function that transformes @r@ occurrences into @r'@
-- occurrences, for every @ix@. In order to associate the index @ix@
-- with the correct system @phi@, the argument to @hmap@ is additionally
-- parameterized by a witness of type @phi ix@. 
hmap  :: (HFunctor phi f) =>
         (forall ix. phi ix -> r ix -> r' ix) ->
         f r ix -> f r' ix
hmap f x = unI0 (hmapA (\ ix x -> I0 (f ix x)) x)

-- | Monadic version of 'hmap'.
hmapM :: (HFunctor phi f, Monad m) =>
         (forall ix. phi ix -> r ix -> m (r' ix)) ->
         f r ix -> m (f r' ix)
hmapM f x = unwrapMonad (hmapA (\ ix x -> WrapMonad (f ix x)) x)
