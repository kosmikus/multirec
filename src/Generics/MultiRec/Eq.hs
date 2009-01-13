{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes       #-}
{-# LANGUAGE TypeOperators    #-}

-----------------------------------------------------------------------------
-- |
-- Module      :  Generics.MultiRec.Eq
-- Copyright   :  (c) 2008--2009 Universiteit Utrecht
-- License     :  BSD3
--
-- Maintainer  :  generics@haskell.org
-- Stability   :  experimental
-- Portability :  non-portable
--
-- Generic equality.
--
-----------------------------------------------------------------------------

module Generics.MultiRec.Eq where

import Generics.MultiRec.Base

-- * Generic equality

class HEq f where
  heq :: s ix ->
         (forall ix. Ix s ix => s ix -> r ix -> r ix -> Bool) ->
         f s r ix -> f s r ix -> Bool

instance HEq (I xi) where
  heq _ eq (I x1) (I x2) = eq index x1 x2

-- | For constant types, we make use of the standard
-- equality function.
instance Eq x => HEq (K x) where
  heq _ eq (K x1) (K x2) = x1 == x2

instance HEq U where
  heq _ eq U U = True

instance (HEq f, HEq g) => HEq (f :+: g) where
  heq ix eq (L x1) (L x2) = heq ix eq x1 x2
  heq ix eq (R y1) (R y2) = heq ix eq y1 y2
  heq _  eq _     _       = False

instance (HEq f, HEq g) => HEq (f :*: g) where
  heq ix eq (x1 :*: y1) (x2 :*: y2) = heq ix eq x1 x2 && heq ix eq y1 y2

-- The following instance does not compile with ghc-6.8.2
instance HEq f => HEq (f :>: ix) where
  heq ix eq (Tag x1) (Tag x2) = heq ix eq x1 x2

instance HEq f => HEq (C c f) where
  heq ix eq (C x1) (C x2) = heq ix eq x1 x2

eq :: (Ix s ix, HEq (PF s)) => s ix -> ix -> ix -> Bool
eq ix x1 x2 = heq ix (\ ix (I0 x1) (I0 x2) -> eq ix x1 x2) (from x1) (from x2)

-- Note:
-- 
-- We do not declare an equality instance such as
--
--   instance (Ix s ix, HEq (PF s)) => Eq ix where
--     (==) = eq index
--
-- because "s" is not mentioned on the right hand side.
-- One datatype may belong to multiple systems, and
-- although the generic equality instances should be
-- the same, there is no good way to decide which instance
-- to use.
--
-- For a concrete "s", it is still possible to manually
-- define an "Eq" instance as above.
