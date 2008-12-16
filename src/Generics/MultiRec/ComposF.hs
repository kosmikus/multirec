{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes       #-}

-----------------------------------------------------------------------------
-- |
-- Module      :  Generics.MultiRec.Compos
-- Copyright   :  (c) 2008 Universiteit Utrecht
-- License     :  BSD3
--
-- Maintainer  :  generics@haskell.org
-- Stability   :  experimental
-- Portability :  non-portable
--
-- The compos operator, inspired by
--
--   B. Bringert and A. Ranta
--   A pattern for almost compositional functions
--   ICFP 2006
--
-----------------------------------------------------------------------------
module Generics.MultiRec.ComposF where

import Control.Monad (liftM)
import Control.Applicative (Applicative(..), liftA)

import Generics.MultiRec.BaseF
import Generics.MultiRec.HFunctorF

-- * Compos

-- | Normal version.
compos :: (Ix s ix, HFunctor (PF s)) =>
          (forall ix. Ix s ix => s ix -> ix e -> ix e) -> ix e -> ix e
compos f = to . hmap (\ ix -> I0 . f ix . unI0) . from

-- | Monadic version of 'compos'.
composM :: (Ix s ix, HFunctor (PF s), Monad m) =>
           (forall ix. Ix s ix => s ix -> ix e -> m (ix e)) -> ix e -> m (ix e)
composM f = liftM to . hmapM (\ ix -> liftM I0 . f ix . unI0) . from

-- | Applicative version of 'compos'.
composA :: (Ix s ix, HFunctor (PF s), Applicative a) =>
           (forall ix. Ix s ix => s ix -> ix e -> a (ix e)) -> ix e -> a (ix e)
composA f = liftA to . hmapA (\ ix -> liftA I0 . f ix . unI0) . from
