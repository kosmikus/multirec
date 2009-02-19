{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE KindSignatures        #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE Rank2Types            #-}
{-# LANGUAGE EmptyDataDecls        #-}

-----------------------------------------------------------------------------
-- |
-- Module      :  Generics.MultiRec.Base
-- Copyright   :  (c) 2008--2009 Universiteit Utrecht
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
   K(..), U(..), E(..), Comp(..), (:+:)(..), (:*:)(..),
   (:>:)(..), unTag,
   C(..), unC,

   -- ** Constructor information
   module Generics.MultiRec.Constructor,

   -- ** Unlifted variants
   I0(..), I0F(..), K0(..),

   -- * Indexed systems
   PF, Str, Ix(..),

   -- * Type level numbers
   Zero, Suc,

   -- * Equality type
   (:=:)(..), Eq_(..)
  ) where

import Control.Applicative
import Generics.MultiRec.Constructor

data Zero
data Suc a

-- * Structure types

infixr 5 :+:
infix  6 :>:
infixr 7 :*:

-- | Represents recursive positions. The first argument indicates
-- which type (within the system) to recurse on.
data I :: * -> ((* -> *) -> * -> *) -> (* -> *) -> (* -> *) -> * -> * where
  I :: Ix s es xi => r xi -> I xi s es r ix

-- | Destructor for 'I'.
unI :: I xi s es r ix -> r xi
unI (I x) = x

-- | Represents constant types that do not belong to the system.
data K a       (s :: (* -> *) -> * -> *) (es :: * -> *) (r :: * -> *) ix = K {unK :: a}

-- | Represents constructors without fields.
data U         (s :: (* -> *) -> * -> *) (es :: * -> *) (r :: * -> *) ix = U

-- | Represents the n'th element type.
data E n       (s :: (* -> *) -> * -> *) (es :: * -> *) (r :: * -> *) ix = E (es n)

-- | Composition of two functors. The outer functor is from BaseF, the
-- inner from Base.
data Comp f (s' :: (* -> *) -> *) (ix' :: * -> *) g (s :: (* -> *) -> * -> *) (es :: * -> *) (r :: * -> *) ix = Comp (f s' I0F (g s es r ix) ix')

-- | Represents sums (choices between constructors).
data (f :+: g) (s :: (* -> *) -> * -> *) (es :: * -> *) (r :: * -> *) ix = L (f s es r ix) | R (g s es r ix)

-- | Represents products (sequences of fields of a constructor).
data (f :*: g) (s :: (* -> *) -> * -> *) (es :: * -> *) (r :: * -> *) ix = f s es r ix :*: g s es r ix

-- | Is used to indicate the type (within the system) that a
-- particular constructor injects to.
data (:>:) :: (((* -> *) -> * -> *) -> (* -> *) -> (* -> *) -> * -> *) -> * -> ((* -> *) -> * -> *) -> (* -> *) -> (* -> *) -> * -> * where
  Tag :: f s es r ix -> (f :>: ix) s es r ix

-- | Destructor for '(:>:)'.
unTag :: (f :>: ix) s es r ix -> f s es r ix
unTag (Tag x) = x

-- | Represents constructors.
data C c f     (s :: (* -> *) -> * -> *) (es :: * -> *) (r :: * -> *) ix where
  C :: (Constructor c) => f s es r ix -> C c f s es r ix

-- | Destructor for 'C'.
unC :: C c f s es r ix -> f s es r ix
unC (C x) = x

-- ** Unlifted variants

-- | Unlifted version of 'I'.
newtype I0 a   = I0 { unI0 :: a }

-- | Unlifted version of 'I' with extra type argument.
newtype I0F e a   = I0F { unI0F :: a e}

-- | Unlifted version of 'K'.
newtype K0 a b = K0 { unK0 :: a }

instance Functor I0 where
  fmap f = I0 . f . unI0

instance Applicative I0 where
  pure              = I0
  (I0 f) <*> (I0 x) = I0 (f x)

instance Functor (K0 a) where
  fmap f = K0 . unK0

-- * Indexed systems

-- | Type family describing the pattern functor of a system.
type family PF (s :: * -> *) :: ((* -> *) -> * -> *) -> (* -> *) -> (* -> *) -> * -> *
type Str s es ix = (PF (s es)) s es I0 ix

class Ix s es ix where
  from_ :: ix -> Str s es ix
  to_   :: Str s es ix -> ix

  -- | Some functions need to have their types desugared in order to make programs
  -- that use them typable.  Desugaring consists in transforming ``inline'' type
  -- family applications into equality constraints. This is a strangeness in current
  -- versions of GHC that hopefully will be fixed sometime in the future.
  from  :: (pfs ~ PF (s es)) => ix -> pfs s es I0 ix
  from = from_
  to    :: (pfs ~ PF (s es)) => pfs s es I0 ix -> ix
  to = to_

  index :: s es ix

infix 4 :=:

data (:=:) :: * -> * -> * where
    Refl :: a :=: a

class Eq_ s where
  eq_ :: s ix -> s ix' -> Maybe (ix :=: ix')
