{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE KindSignatures        #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE LiberalTypeSynonyms   #-}
{-# LANGUAGE Rank2Types            #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE GADTs                 #-}

-----------------------------------------------------------------------------
-- |
-- Module      :  Generics.MultiRec.FoldAlgK
-- Copyright   :  (c) 2009--2010 Universiteit Utrecht
-- License     :  BSD3
--
-- Maintainer  :  generics@haskell.org
-- Stability   :  experimental
-- Portability :  non-portable
--
-- A variant of fold that allows the specification of the algebra in a
-- convenient way, and that fixes the result type to a constant.
--
-----------------------------------------------------------------------------

module Generics.MultiRec.FoldAlgK where

import Generics.MultiRec.Base
import Generics.MultiRec.HFunctor

-- * The type family of convenient algebras.

-- | The type family we use to describe the convenient algebras.
type family Alg (f :: (* -> *) -> * -> *) 
                (r :: *)           -- result type
                :: *

-- | For a constant, we take the constant value to a result.
type instance Alg (K a) r = a -> r

-- | For a unit, no arguments are available.
type instance Alg U r = r

-- | For an identity, we turn the recursive result into a final result.
--   Note that the index can change.
type instance Alg (I xi) r = r -> r

-- | For a sum, the algebra is a pair of two algebras.
type instance Alg (f :+: g) r = (Alg f r, Alg g r)

-- | For a product where the left hand side is a constant, we
--   take the value as an additional argument.
type instance Alg (K a :*: g) r = a -> Alg g r

-- | For a product where the left hand side is an identity, we
--   take the recursive result as an additional argument.
type instance Alg (I xi :*: g) r = r -> Alg g r

-- | Tags are ignored.
type instance Alg (f :>: xi) r = Alg f r

-- | Constructors are ignored.
type instance Alg (C c f) r = Alg f r

-- | The algebras passed to the fold have to work for all index types
--   in the family. The additional witness argument is required only
--   to make GHC's typechecker happy.
type Algebra phi r = forall ix. phi ix -> Alg (PF phi) r

-- * The class to turn convenient algebras into standard algebras.

-- | The class fold explains how to convert a convenient algebra
--   'Alg' back into a function from functor to result, as required
--   by the standard fold function.
class Fold (f :: (* -> *) -> * -> *) where
  alg :: Alg f r -> f (K0 r) ix -> r

instance Fold (K a) where
  alg f (K x) = f x

instance Fold U where
  alg f U     = f

instance Fold (I xi) where
  alg f (I (K0 x)) = f x

instance (Fold f, Fold g) => Fold (f :+: g) where
  alg (f, g) (L x) = alg f x
  alg (f, g) (R x) = alg g x

instance (Fold g) => Fold (K a :*: g) where
  alg f (K x :*: y) = alg (f x) y

instance (Fold g) => Fold (I xi :*: g) where
  alg f (I (K0 x) :*: y) = alg (f x) y

instance (Fold f) => Fold (f :>: xi) where
  alg f (Tag x) = alg f x

instance (Fold f) => Fold (C c f) where
  alg f (C x) = alg f x

-- * Interface

-- | Fold with convenient algebras.
fold :: forall phi ix r . (Fam phi, HFunctor phi (PF phi), Fold (PF phi)) =>
        Algebra phi r -> phi ix -> ix -> r
fold f p = alg (f p) .
           hmap (\ p (I0 x) -> K0 (fold f p x)) p .
           from p

-- * Construction of algebras

infixr 5 &

-- | For constructing algebras that are made of nested pairs rather
--   than n-ary tuples, it is helpful to use this pairing combinator.
(&) :: a -> b -> (a, b)
(&) = (,)
