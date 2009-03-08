{-# LANGUAGE KindSignatures   #-}
{-# LANGUAGE TypeFamilies     #-}
{-# LANGUAGE FlexibleContexts #-}

-----------------------------------------------------------------------------
-- |
-- Module      :  Generics.MultiRec.HFix
-- Copyright   :  (c) 2008--2009 Universiteit Utrecht
-- License     :  BSD3
--
-- Maintainer  :  generics@haskell.org
-- Stability   :  experimental
-- Portability :  non-portable
--
-- Higher-order fixed point operator as well as conversion functions.
-- It is rarely necessary to use 'HFix'. Generic functions
-- usually convert between the original datatype and the functor directly.
--
-----------------------------------------------------------------------------

module Generics.MultiRec.HFix where

import Generics.MultiRec.Base
import Generics.MultiRec.HFunctor
import Generics.MultiRec.Fold

-- * Fixed point of indexed types

data HFix (h :: (* -> *) -> * -> *) ix = HIn { hout :: h (HFix h) ix }

hfrom :: (Fam phi, HFunctor phi (PF phi)) => phi ix -> ix -> HFix (PF phi) ix
hfrom = fold (const HIn)

hto :: (Fam phi, HFunctor phi (PF phi)) => phi ix -> HFix (PF phi) ix -> ix
hto = unfold (const hout)
