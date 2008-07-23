{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE KindSignatures        #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE Rank2Types            #-}

module Generics.MultiRec.Base where

import Control.Applicative

-- * Structure types

infixr 5 :+:
infix  6 :>:
infixr 7 :*:

data I :: * -> (* -> *) -> (* -> *) -> * -> * where
  I :: Ix s xi => r xi -> I xi s r ix

unI :: I xi s r ix -> r xi
unI (I x) = x

data K a       (s :: * -> *) (r :: * -> *) ix = K {unK :: a}

data (f :+: g) (s :: * -> *) (r :: * -> *) ix = L (f s r ix) | R (g s r ix)
data (f :*: g) (s :: * -> *) (r :: * -> *) ix = f s r ix :*: g s r ix

data (:>:) :: ((* -> *) -> (* -> *) -> * -> *) -> * -> (* -> *) -> (* -> *) -> * -> * where
  Tag { unTag :: f s r ix } :: (f :>: ix) s r ix

-- ** Unlifted variants

newtype I0 a   = I0 { unI0 :: a }
newtype K0 a b = K0 { unK0 :: a }

instance Functor I0 where
  fmap f = I0 . f . unI0

instance Applicative I0 where
  pure              = I0
  (I0 f) <*> (I0 x) = I0 (f x)

-- * Indexed families

type family PF s :: (* -> *) -> (* -> *) -> * -> *
type Str s ix = (PF s) s I0 ix

-- | Some functions need to have their types desugared in order to make programs
-- that use them typable.  Desugaring consists in transforming ``inline'' type
-- family applications into equality constraints. This is a strangeness in current
-- versions of GHC that hopefully will be fixed sometime in the future.
class Ix s ix where
  from  :: (pfs ~ PF s) => ix -> pfs s I0 ix
  to    :: (pfs ~ PF s) => pfs s I0 ix -> ix
  index :: s ix

-- * Fixed point of indexed types

data HFix (h :: (* -> *) -> * -> *) ix = HIn { hout :: h (HFix h) ix }

