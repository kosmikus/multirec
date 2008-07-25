{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE KindSignatures        #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE Rank2Types            #-}

module Generics.MultiRec.Base 
  (-- * Structure types
   I(..), unI,
   K(..), (:+:)(..), (:*:)(..),
   (:>:)(..), unTag,

   -- ** Unlifted variants
   I0(..), K0(..),

   -- * Indexed systems
   PF, Str, Ix(..)
  ) where

import Control.Applicative

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
