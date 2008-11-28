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

module Generics.MultiRec.BaseF 
  (-- * Structure types
   I(..), unI,
   K(..), (:+:)(..), (:*:)(..),
   (:>:)(..), unTag,
   E(..),

   -- ** Unlifted variants
   I0(..), K0(..),

   -- * Indexed systems
   PF, Str, Ix(..),

   -- * Equality type
   (:=:)(..), Eq_(..)
  ) where

import Control.Applicative

-- * Structure types

infixr 5 :+:
infix  6 :>:
infixr 7 :*:

data ListU :: (* -> *) -> * where
    List :: ListU []

type instance PF ListU = K () :>: []
                     :+: E :*: I [] :>: []

instance Ix ListU [] where
    from_ [] = L (Tag (K ()))
    from_ (x : xs) = R (Tag (E x :*: I (I0 xs)))
    to_ (L (Tag (K ()))) = []
    to_ (R (Tag (E x :*: I (I0 xs)))) = x : xs
    index = List

-- | Represents recursive positions. The first argument indicates
-- which type (within the system) to recurse on.
data I :: (* -> *) -> ((* -> *) -> *) -> (* -> (* -> *) -> *) -> * -> (* -> *) -> * where
  I :: Ix s xi => r e xi -> I xi s r e ix

-- | Destructor for 'I'.
unI :: I xi s r e ix -> r e xi
unI (I x) = x

-- | Represents constant types that do not belong to the system.
data K a       (s :: (* -> *) -> *) (r :: * -> (* -> *) -> *) e (ix :: * -> *) = K {unK :: a}

-- | Represents element types that do not belong to the system.
data E (s :: (* -> *) -> *) (r :: * -> (* -> *) -> *) e (ix :: * -> *) = E {unE :: e}

-- | Represents sums (choices between constructors).
data (f :+: g) (s :: (* -> *) -> *) (r :: * -> (* -> *) -> *) e (ix :: * -> *) = L (f s r e ix) | R (g s r e ix)

-- | Represents products (sequences of fields of a constructor).
data (f :*: g) (s :: (* -> *) -> *) (r :: * -> (* -> *) -> *) e (ix :: * -> *) = f s r e ix :*: g s r e ix

-- | Is used to indicate the type (within the system) that a
-- particular constructor injects to.
data (:>:) :: (((* -> *) -> *) -> (* -> (* -> *) -> *) -> * -> (* -> *) -> *) -> (* -> *) -> ((* -> *) -> *) -> (* -> (* -> *) -> *) -> * -> (* -> *) -> * where
  Tag :: f s r e ix -> (f :>: ix) s r e ix

-- | Destructor for '(:>:)'.
unTag :: (f :>: ix) s r e ix -> f s r e ix
unTag (Tag x) = x

-- ** Unlifted variants

-- | Unlifted version of 'I'.
newtype I0 e a   = I0 { unI0 :: a e}

-- | Unlifted version of 'K'.
newtype K0 a b = K0 { unK0 :: a }

{-
instance Functor I0 where
  fmap f = I0 . f . unI0

instance Applicative I0 where
  pure              = I0
  (I0 f) <*> (I0 x) = I0 (f x)
  -}

-- * Indexed systems

-- | Type family describing the pattern functor of a system.
type family PF s :: ((* -> *) -> *) -> (* -> (* -> *) -> *) -> * -> (* -> *) -> *
type Str s e ix = (PF s) s I0 e ix

class Ix s ix where
  from_ :: ix e -> Str s e ix
  to_   :: Str s e ix -> ix e

  -- | Some functions need to have their types desugared in order to make programs
  -- that use them typable.  Desugaring consists in transforming ``inline'' type
  -- family applications into equality constraints. This is a strangeness in current
  -- versions of GHC that hopefully will be fixed sometime in the future.
  from  :: (pfs ~ PF s) => ix e -> pfs s I0 e ix
  from = from_
  to    :: (pfs ~ PF s) => pfs s I0 e ix -> ix e
  to = to_

  index :: s ix

infix 4 :=:

data (:=:) :: * -> * -> * where
    Refl :: a :=: a

class Eq_ s where
  eq_ :: s ix -> s ix' -> Maybe (ix :=: ix')
