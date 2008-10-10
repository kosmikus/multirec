{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes       #-}
{-# LANGUAGE TypeOperators    #-}
{-# LANGUAGE TypeFamilies #-}

module Generics.MultiRec.Eq where

import Generics.MultiRec.Base

class HEq f where
  heq :: s ix ->
         (forall ix. Ix s ix => s ix -> r ix -> r ix -> Bool) ->
         f s r ix -> f s r ix -> Bool

instance HEq (I xi) where
  heq _ eq (I x1) (I x2) = eq index x1 x2

instance Eq x => HEq (K x) where
  heq _ eq (K x1) (K x2) = x1 == x2

instance (HEq f, HEq g) => HEq (f :+: g) where
  heq ix eq (L x1) (L x2) = heq ix eq x1 x2
  heq ix eq (R y1) (R y2) = heq ix eq y1 y2
  heq _  eq _     _       = False

instance (HEq f, HEq g) => HEq (f :*: g) where
  heq ix eq (x1 :*: y1) (x2 :*: y2) = heq ix eq x1 x2 && heq ix eq y1 y2

instance HEq f => HEq (f :>: ix) where
  heq ix eq (Tag x1) (Tag x2) = heq ix eq x1 x2

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
