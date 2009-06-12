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
compos :: (Fam phi, HFunctor phi (PF phi)) =>
          (forall ix. phi ix -> ix -> ix) -> phi ix -> ix -> ix
compos f p = to p . hmap (\ p -> I0 . f p . unI0) p . from p

-- | Monadic version of 'compos'.
composM :: (Fam phi, HFunctor phi (PF phi), Monad m) =>
           (forall ix. phi ix -> ix -> m ix) -> phi ix -> ix -> m ix
composM f p = liftM (to p) . hmapM (\ p -> liftM I0 . f p . unI0) p . from p

-- | Applicative version of 'compos'.
composA :: (Fam phi, HFunctor phi (PF phi), Applicative a) =>
           (forall ix. phi ix -> ix -> a ix) -> phi ix -> ix -> a ix
composA f p = liftA (to p) . hmapA (\ p -> liftA I0 . f p . unI0) p . from p
