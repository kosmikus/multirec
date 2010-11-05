{-# LANGUAGE GADTs          #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeOperators  #-}

-----------------------------------------------------------------------------
-- |
-- Module      :  Generics.MultiRec.TEq
-- Copyright   :  (c) 2008--2010 Universiteit Utrecht
-- License     :  BSD3
--
-- Maintainer  :  generics@haskell.org
-- Stability   :  experimental
-- Portability :  non-portable
--
-- Type-level equality. This module is currently provided by the multirec
-- library, even though it is more general and does not really belong here.
-- 
-----------------------------------------------------------------------------
module Generics.MultiRec.TEq where

infix 4 :=:

data (:=:) :: * -> * -> * where
  Refl :: a :=: a

cast :: a :=: b -> a -> b
cast Refl x = x
