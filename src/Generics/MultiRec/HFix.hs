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

-- * Fixed point of indexed types

data HFix (h :: (* -> *) -> * -> *) ix = HIn { hout :: h (HFix h) ix }

hfrom :: (pfs ~ PF s, Ix s ix, HFunctor (PF s)) => ix -> HFix (pfs s) ix
hfrom = HIn . hmap (const (hfrom . unI0)) . from

hto :: (pfs ~ PF s, Ix s ix, HFunctor (PF s)) => HFix (pfs s) ix -> ix
hto = to . hmap (const (I0 . hto)) . hout
