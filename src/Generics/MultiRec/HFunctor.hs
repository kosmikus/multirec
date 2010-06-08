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
import Data.Traversable (Traversable(..))

import Generics.MultiRec.Base

-- * Generic map

-- We define a general 'hmapA' that works on applicative functors.
-- The simpler 'hmap' is a special case.

class HFunctor phi f where
  hmapA :: (Applicative a) =>
           (forall ix. phi ix -> r ix -> a (r' ix)) ->
           phi ix -> f r ix -> a (f r' ix)

instance El phi xi => HFunctor phi (I xi) where
  hmapA f _ (I x) = I <$> f proof x

instance HFunctor phi (K x) where
  hmapA _ _ (K x) = pure (K x)

instance HFunctor phi U where
  hmapA _ _ U = pure U

instance (HFunctor phi f, HFunctor phi g) => HFunctor phi (f :+: g) where
  hmapA f p (L x) = L <$> hmapA f p x
  hmapA f p (R y) = R <$> hmapA f p y

instance (HFunctor phi f, HFunctor phi g) => HFunctor phi (f :*: g) where
  hmapA f p (x :*: y) = (:*:) <$> hmapA f p x <*> hmapA f p y

instance HFunctor phi f => HFunctor phi (f :>: ix) where
  hmapA f p (Tag x) = Tag <$> hmapA f p x

instance (Traversable f, HFunctor phi g) => HFunctor phi (f :.: g) where
  hmapA f p (D x) = D <$> traverse (hmapA f p) x

instance (Constructor c, HFunctor phi f) => HFunctor phi (C c f) where
  hmapA f p (C x) = C <$> hmapA f p x

-- | The function 'hmap' takes a functor @f@. All the recursive instances
-- in that functor are wrapped by an application of @r@. The argument to
-- 'hmap' takes a function that transformes @r@ occurrences into @r'@
-- occurrences, for every @ix@. In order to associate the index @ix@
-- with the correct family @phi@, the argument to @hmap@ is additionally
-- parameterized by a witness of type @phi ix@. 
hmap  :: (HFunctor phi f) =>
         (forall ix. phi ix -> r ix -> r' ix) ->
         phi ix -> f r ix -> f r' ix
hmap f p x = unI0 (hmapA (\ ix x -> I0 (f ix x)) p x)

-- | Monadic version of 'hmap'.
hmapM :: (HFunctor phi f, Monad m) =>
         (forall ix. phi ix -> r ix -> m (r' ix)) ->
         phi ix -> f r ix -> m (f r' ix)
hmapM f p x = unwrapMonad (hmapA (\ ix x -> WrapMonad (f ix x)) p x)
