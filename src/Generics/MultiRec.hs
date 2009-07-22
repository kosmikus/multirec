-----------------------------------------------------------------------------
-- |
-- Module      :  Generics.MultiRec
-- Copyright   :  (c) 2008 Universiteit Utrecht
-- License     :  BSD3
--
-- Maintainer  :  generics@haskell.org
-- Stability   :  experimental
-- Portability :  non-portable
--
-- multirec --
-- generic programming for families of recursive datatypes
-- 
-- This top-level module re-exports most modules of the library.
--
-----------------------------------------------------------------------------

module Generics.MultiRec
  (
    -- * Base
    module Generics.MultiRec.Base,
    
    -- * Generic functions
    module Generics.MultiRec.HFunctor,
    module Generics.MultiRec.Fold,
    module Generics.MultiRec.Compos,
    module Generics.MultiRec.Eq,
    module Generics.MultiRec.HFix,
    module Generics.MultiRec.Show,
    module Generics.MultiRec.Read
  )
  where

import Generics.MultiRec.Base
import Generics.MultiRec.HFunctor
import Generics.MultiRec.Fold
import Generics.MultiRec.Compos
import Generics.MultiRec.Eq
import Generics.MultiRec.HFix
import Generics.MultiRec.Show
import Generics.MultiRec.Read


