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
-- Copyright   :  (c) 2008 Universiteit Utrecht
-- License     :  BSD3
--
-- Maintainer  :  generics@haskell.org
-- Stability   :  experimental
-- Portability :  non-portable
--
-- This module is the base of the multirec library. It defines the view of a
-- system of datatypes: All the datatypes of the system are represented as
-- indexed functors that are built up from the structure types defined in this
-- module. Furthermore, in order to use the library for a system, conversion
-- functions have to be defined between the original datatypes and their
-- representation. The type class that holds these conversion functions are
-- also defined here.
--
-----------------------------------------------------------------------------

module Generics.MultiRec.Base 
  (-- * Structure types
   I(..), unI,
   K(..), (:+:)(..), (:*:)(..),
   (:>:)(..), unTag,
   C(..), unC,

   -- ** Constructor information
   module Generics.MultiRec.Constructor,

   -- ** Unlifted variants
   I0(..), K0(..),

   -- * Indexed systems
   PF, Str, Ix(..),

   -- * Equality type
   (:=:)(..), Eq_(..)
  ) where

import Control.Applicative
import Generics.MultiRec.Constructor

-- * Structure types

infixr 5 :+:
infix  6 :>:
infixr 7 :*:

-- | Represents recursive positions. The first argument indicates
-- which type (within the system) to recurse on.
data I :: * -> (* -> *) -> (* -> *) -> * -> * where
  I :: Ix s xi => r xi -> I xi s r ix

-- | Destructor for 'I'.
unI :: I xi s r ix -> r xi
unI (I x) = x

-- | Represents constant types that do not belong to the system.
data K a       (s :: * -> *) (r :: * -> *) ix = K {unK :: a}

-- | Represents sums (choices between constructors).
data (f :+: g) (s :: * -> *) (r :: * -> *) ix = L (f s r ix) | R (g s r ix)

-- | Represents products (sequences of fields of a constructor).
data (f :*: g) (s :: * -> *) (r :: * -> *) ix = f s r ix :*: g s r ix

-- | Is used to indicate the type (within the system) that a
-- particular constructor injects to.
data (:>:) :: ((* -> *) -> (* -> *) -> * -> *) -> * -> (* -> *) -> (* -> *) -> * -> * where
  Tag :: f s r ix -> (f :>: ix) s r ix

-- | Destructor for '(:>:)'.
unTag :: (f :>: ix) s r ix -> f s r ix
unTag (Tag x) = x

-- | Represents constructors.
data C c f     (s :: * -> *) (r :: * -> *) ix where
  C :: (Constructor c) => f s r ix -> C c f s r ix

-- | Destructor for 'C'.
unC :: C c f s r ix -> f s r ix
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

-- * Indexed systems

-- | Type family describing the pattern functor of a system.
type family PF s :: (* -> *) -> (* -> *) -> * -> *
type Str s ix = (PF s) s I0 ix

class Ix s ix where
  from_ :: ix -> Str s ix
  to_   :: Str s ix -> ix

  -- | Some functions need to have their types desugared in order to make programs
  -- that use them typable.  Desugaring consists in transforming ``inline'' type
  -- family applications into equality constraints. This is a strangeness in current
  -- versions of GHC that hopefully will be fixed sometime in the future.
  from  :: (pfs ~ PF s) => ix -> pfs s I0 ix
  from = from_
  to    :: (pfs ~ PF s) => pfs s I0 ix -> ix
  to = to_

  index :: s ix

infix 4 :=:

data (:=:) :: * -> * -> * where
    Refl :: a :=: a

class Eq_ s where
  eq_ :: s ix -> s ix' -> Maybe (ix :=: ix')
