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
