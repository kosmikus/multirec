{-# LANGUAGE EmptyDataDecls        #-}
{-# LANGUAGE TemplateHaskell       #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE KindSignatures        #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module GRose where

-- Test case for Issue #1.

import Generics.MultiRec.Base
import Generics.MultiRec.TH

data GRose a = Leaf a | Node [GRose a]

data GRoseF :: * -> * -> * where
  GRose :: GRoseF a (GRose a)

$(deriveAll ''GRoseF)

-- Desired output:
--
-- data Leaf
-- data Node
--
-- instance Constructor Leaf where
--   conName _ = "Leaf"
-- instance Constructor Node where
--   conName _ = "Node"
--
-- type instance PF (GRoseF a) =
--   (:>:) ((:+:) (C Leaf (K a)) (C Node ((:.:) [] (I (GRose a))))) (GRose a)
--
-- instance El (GRoseF a) (GRose a) where
--   proof = GRose
--
-- instance Fam (GRoseF a) where
--
--   from GRose (Leaf f0) = Tag (L (C (K f0)))
--   from GRose (Node f0) = Tag (R (C ((D . (fmap (I . I0))) f0)))
--
--   to GRose (Tag (L (C f0))) = Leaf (unK f0)
--   to GRose (Tag (R (C f0))) = Node (((fmap (unI0 . unI)) . unD) f0)
--
-- instance EqS (GRoseF a) where
--   eqS GRose GRose = Just Refl
