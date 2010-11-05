{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes       #-}
{-# LANGUAGE TypeOperators    #-}
{-# LANGUAGE KindSignatures   #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE PatternSignatures #-}

-----------------------------------------------------------------------------
-- |
-- Module      :  Generics.MultiRec.ConNames
-- Copyright   :  (c) 2008--2010 Universiteit Utrecht
-- License     :  BSD3
--
-- Maintainer  :  generics@haskell.org
-- Stability   :  experimental
-- Portability :  non-portable
--
-- Generic function that returns the constructor names available in a family
-- of datatypes.
--
-----------------------------------------------------------------------------

module Generics.MultiRec.ConNames where

import Generics.MultiRec.Base
import Generics.MultiRec.Constructor

class ConNames (f :: (* -> *) -> * -> *) where
  hconNames :: f r ix -> [String]

instance Constructor c => ConNames (C c f) where
  hconNames c = [conName c]

instance (ConNames f, ConNames g) => ConNames (f :+: g) where
  hconNames (_ :: (f :+: g) r ix) = hconNames (undefined :: f r ix) ++
                                    hconNames (undefined :: g r ix)

instance ConNames (K x) where
  hconNames _ = []

instance ConNames U where
  hconNames _ = []

instance ConNames (f :*: g) where
  hconNames _ = []

instance ConNames (I a) where
  hconNames _ = []

instance (ConNames f) => ConNames (f :>: ix) where
  hconNames (_ :: (f :>: ix) r xi) = hconNames (undefined :: f r ix)

conNames :: forall phi ix . (ConNames (PF phi)) => phi ix -> [String]
conNames _ = hconNames (undefined :: PF phi I0 ix)
