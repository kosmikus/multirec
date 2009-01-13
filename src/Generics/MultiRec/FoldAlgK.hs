{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE KindSignatures        #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE LiberalTypeSynonyms   #-}
{-# LANGUAGE Rank2Types            #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE FlexibleInstances     #-}

-----------------------------------------------------------------------------
-- |
-- Module      :  Generics.MultiRec.FoldAlgK
-- Copyright   :  (c) 2009 Universiteit Utrecht
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
type family Alg (f :: (* -> *) -> (* -> *) -> * -> *) 
                (s :: * -> *)      -- system
                (r :: *)           -- result type
                :: *

-- | For a constant, we take the constant value to a result.
type instance Alg (K a) (s :: * -> *) r = a -> r

-- | For a unit, no arguments are available.
type instance Alg U (s :: * -> *) r = r

-- | For an identity, we turn the recursive result into a final result.
--   Note that the index can change.
type instance Alg (I xi) (s :: * -> *) r = r -> r

-- | For a sum, the algebra is a pair of two algebras.
type instance Alg (f :+: g) s r = (Alg f s r, Alg g s r)

-- | For a product where the left hand side is a constant, we
--   take the value as an additional argument.
type instance Alg (K a :*: g) s r = a -> Alg g s r

-- | For a product where the left hand side is an identity, we
--   take the recursive result as an additional argument.
type instance Alg (I xi :*: g) s r = r -> Alg g s r

-- | A tag changes the index of the final result.
type instance Alg (f :>: xi) s r = Alg f s r

-- | Constructors are ignored.
type instance Alg (C c f) s r = Alg f s r

-- | The algebras passed to the fold have to work for all index types
--   in the system. The additional witness argument is required only
--   to make GHC's typechecker happy.
type Algebra s r = forall ix. Ix s ix => s ix -> Alg (PF s) s r

-- * The class to turn convenient algebras into standard algebras.

-- | The class fold explains how to convert a convenient algebra
--   'Alg' back into a function from functor to result, as required
--   by the standard fold function.
class Fold (f :: (* -> *) -> (* -> *) -> * -> *) where
  alg :: (Ix s ix) => Alg f s r -> f s (K0 r) ix -> r

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

-- | Variant of fold that takes an additional witness argument.
fold' :: forall s ix r . (Ix s ix, HFunctor (PF s), Fold (PF s)) =>
         s ix ->
         Algebra s r ->
         ix -> r
fold' ix f = (alg :: Alg (PF s) s r -> (PF s) s (K0 r) ix -> r) (f ix) .
             hmap (\ _ (I0 x) -> K0 (fold' index f x)) .
             from

-- | Fold with convenient algebras.
fold :: forall s ix r . (Ix s ix, HFunctor (PF s), Fold (PF s)) =>
        Algebra s r ->
        ix -> r
fold = fold' index

-- * Construction of algebras

infixr 5 &

-- | For constructing algebras that are made of nested pairs rather
--   than n-ary tuples, it is helpful to use this pairing combinator.
(&) :: a -> b -> (a, b)
(&) = (,)
