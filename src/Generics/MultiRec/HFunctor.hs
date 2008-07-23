{-# LANGUAGE GADTs         #-}
{-# LANGUAGE RankNTypes    #-}
{-# LANGUAGE TypeOperators #-}

module Generics.MultiRec.HFunctor where

import Control.Monad (liftM, liftM2)
import Control.Applicative (Applicative(..), liftA, liftA2, WrappedMonad(..))

import Generics.MultiRec.Base

-- * Generic map

-- Deviating from the paper, we define an 'hmapA' that works
-- on applicative functors. The original 'hmap' as given in the
-- paper is a special case.

class HFunctor f where
  hmapA :: (Applicative a) =>
           (forall ix. Ix s ix => s ix -> r ix -> a (r' ix)) ->
           f s r ix -> a (f s r' ix)

instance HFunctor (I xi) where
  hmapA f (I x) = liftA I (f index x)

instance HFunctor (K x) where
  hmapA _ (K x)  = pure (K x)

instance (HFunctor f, HFunctor g) => HFunctor (f :+: g) where
  hmapA f (L x) = liftA L (hmapA f x)
  hmapA f (R y) = liftA R (hmapA f y)

instance (HFunctor f, HFunctor g) => HFunctor (f :*: g) where
  hmapA f (x :*: y) = liftA2 (:*:) (hmapA f x) (hmapA f y)

instance HFunctor f => HFunctor (f :>: ix) where
  hmapA f (Tag x) = liftA Tag (hmapA f x)


hmap  :: (HFunctor f) =>
         (forall ix. Ix s ix => s ix -> r ix -> r' ix) ->
         f s r ix -> f s r' ix
hmap f x = unI0 (hmapA (\ ix x -> I0 (f ix x)) x)

hmapM :: (HFunctor f, Monad m) =>
         (forall ix. Ix s ix => s ix -> r ix -> m (r' ix)) ->
         f s r ix -> m (f s r' ix)
hmapM f x = unwrapMonad (hmapA (\ ix x -> WrapMonad (f ix x)) x)
