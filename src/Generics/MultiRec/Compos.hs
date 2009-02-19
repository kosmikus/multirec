{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes       #-}

-----------------------------------------------------------------------------
-- |
-- Module      :  Generics.MultiRec.Compos
-- Copyright   :  (c) 2008--2009 Universiteit Utrecht
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

module Generics.MultiRec.Compos where

import Control.Monad (liftM)
import Control.Applicative (Applicative(..), liftA)

import Generics.MultiRec.Base
import Generics.MultiRec.HFunctor

-- * Compos

-- | Normal version.
compos :: (Ix s es ix, HFunctor (PF (s es))) =>
          (forall ix. Ix s es ix => s es ix -> ix -> ix) -> ix -> ix
compos f = to . hmap (\ ix -> I0 . f ix . unI0) . from

-- | Monadic version of 'compos'.
composM :: (Ix s es ix, HFunctor (PF (s es)), Monad m) =>
           (forall ix. Ix s es ix => s es ix -> ix -> m ix) -> ix -> m ix
composM f = liftM to . hmapM (\ ix -> liftM I0 . f ix . unI0) . from

-- | Applicative version of 'compos'.
composA :: (Ix s es ix, HFunctor (PF (s es)), Applicative a) =>
           (forall ix. Ix s es ix => s es ix -> ix -> a ix) -> ix -> a ix
composA f = liftA to . hmapA (\ ix -> liftA I0 . f ix . unI0) . from
