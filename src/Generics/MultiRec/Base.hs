{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE KindSignatures        #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE Rank2Types            #-}

-----------------------------------------------------------------------------
-- |
-- Module      :  Generics.MultiRec.Base
-- Copyright   :  (c) 2008--2010 Universiteit Utrecht
-- License     :  BSD3
--
-- Maintainer  :  generics@haskell.org
-- Stability   :  experimental
-- Portability :  non-portable
--
-- This module is the base of the multirec library. It defines the view of a
-- family of datatypes: All the datatypes of the family are represented as
-- indexed functors that are built up from the structure types defined in this
-- module. Furthermore, in order to use the library for a family, conversion
-- functions have to be defined between the original datatypes and their
-- representation. The type class that holds these conversion functions are
-- also defined here.
--
-----------------------------------------------------------------------------

module Generics.MultiRec.Base 
  (-- * Structure types
   I(..),
   K(..), U(..), (:+:)(..), (:*:)(..),
   (:>:)(..), unTag,
   (:.:)(..),
   C(..), unC,

   -- ** Constructor information
   module Generics.MultiRec.Constructor,

   -- ** Unlifted variants
   I0(..), K0(..),

   -- * Indexed families
   PF, El(..), Fam(..), index,

   -- ** Equality for indexed families
   module Generics.MultiRec.TEq,
   EqS(..)
  ) where

import Control.Applicative
import Generics.MultiRec.Constructor
import Generics.MultiRec.TEq

-- * Structure types

infixr 5 :+:
infix  6 :>:
infixr 7 :*:

-- | Represents recursive positions. The first argument indicates
-- which type to recurse on.
data I xi      (r :: * -> *) ix = I {unI :: r xi}

-- | Represents constant types that do not belong to the family.
data K a       (r :: * -> *) ix = K {unK :: a}

-- | Represents constructors without fields.
data U         (r :: * -> *) ix = U

-- | Represents sums (choices between constructors).
data (f :+: g) (r :: * -> *) ix = L (f r ix) | R (g r ix)

-- | Represents products (sequences of fields of a constructor).
data (f :*: g) (r :: * -> *) ix = f r ix :*: g r ix

-- | Is used to indicate the type that a
-- particular constructor injects to.
data f :>: ix :: (* -> *) -> * -> * where
  Tag :: f r ix -> (f :>: ix) r ix

-- | Destructor for '(:>:)'.
unTag :: (f :>: ix) r ix -> f r ix
unTag (Tag x) = x

-- | Represents composition with functors
-- of kind * -> *.
data (f :.: g) (r :: * -> *) ix = D {unD :: f (g r ix)}

-- | Represents constructors.
data C c f     (r :: * -> *) ix where
  C :: f r ix -> C c f r ix

-- | Destructor for 'C'.
unC :: C c f r ix -> f r ix
unC (C x) = x

-- ** Unlifted variants

-- | Unlifted version of 'I'.
newtype I0 a   = I0 { unI0 :: a }

-- | Unlifted version of 'K'.
newtype K0 a b = K0 { unK0 :: a }

instance Functor I0 where
  fmap f = I0 . f . unI0

instance Applicative I0 where
  pure              = I0
  (I0 f) <*> (I0 x) = I0 (f x)

instance Functor (K0 a) where
  fmap f = K0 . unK0

-- * Indexed families

-- | Type family describing the pattern functor of a family.
type family PF phi :: (* -> *) -> * -> *

-- | Class for the members of a family.
class El phi ix where
  proof :: phi ix

-- | For backwards-compatibility: a synonym for 'proof'.
index :: El phi ix => phi ix
index = proof

-- | Class that contains the shallow conversion functions for a family.
class Fam phi where
  from :: phi ix -> ix -> PF phi I0 ix
  to   :: phi ix -> PF phi I0 ix -> ix

-- | Semi-decidable equality for types of a family.
class EqS phi where
  eqS :: phi ix -> phi ix' -> Maybe (ix :=: ix')

