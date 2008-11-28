{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes       #-}
{-# LANGUAGE TypeOperators    #-}
{-# LANGUAGE TypeFamilies     #-}

-----------------------------------------------------------------------------
-- |
-- Module      :  Generics.MultiRec.Eq
-- Copyright   :  (c) 2008 Universiteit Utrecht
-- License     :  BSD3
--
-- Maintainer  :  generics@haskell.org
-- Stability   :  experimental
-- Portability :  non-portable
--
-- Generic equality.
--
-----------------------------------------------------------------------------
module Generics.MultiRec.EqF where

import Generics.MultiRec.BaseF

-- * Generic equality

class HEq f where
  heq :: s ix ->
         (forall ix. Ix s ix => s ix -> r e ix -> r e ix -> Bool) ->
         (e -> e -> Bool) ->
         f s r e ix -> f s r e ix -> Bool

instance HEq (I xi) where
  heq _ eq eqE (I x1) (I x2) = eq index x1 x2

instance Eq x => HEq (K x) where
  heq _ eq eqE (K x1) (K x2) = x1 == x2

instance HEq E where
  heq _ eq eqE (E e1) (E e2) = e1 `eqE` e2

instance (HEq f, HEq g) => HEq (f :+: g) where
  heq ix eq eqE (L x1) (L x2) = heq ix eq eqE x1 x2
  heq ix eq eqE (R y1) (R y2) = heq ix eq eqE y1 y2
  heq _  eq eqE _     _       = False

instance (HEq f, HEq g) => HEq (f :*: g) where
  heq ix eq eqE (x1 :*: y1) (x2 :*: y2) = heq ix eq eqE x1 x2 && heq ix eq eqE y1 y2

-- The following instance does not compile with ghc-6.8.2
instance HEq f => HEq (f :>: ix) where
  heq ix eq eqE (Tag x1) (Tag x2) = heq ix eq eqE x1 x2

eq :: (Ix s ix, HEq (PF s), Eq e) => s ix -> ix e -> ix e -> Bool
eq ix x1 x2 = heq ix (\ ix (I0 x1) (I0 x2) -> eq ix x1 x2) (==) (from x1) (from x2)

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
