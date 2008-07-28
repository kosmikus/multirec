{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE KindSignatures        #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE LiberalTypeSynonyms   #-}
{-# LANGUAGE Rank2Types            #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Generics.MultiRec.BetterFold where

import Generics.MultiRec.Base
import Generics.MultiRec.HFunctor

type family Alg (f :: (* -> *) -> (* -> *) -> * -> *) 
     :: (* -> *) ->      -- system s
        (* -> *) ->      -- recursive positions r
        (* -> *) ->      -- continuation k
        * ->             -- index ix
        * 

type instance Alg (K a) = AlgK a
type AlgK a (s :: * -> *) (r :: * -> *) k ix = a -> k ix

type instance Alg (I xi) = AlgI xi
type AlgI xi (s :: * -> *) r k ix = r xi -> k ix

type instance Alg (f :+: g) = AlgS f g
type AlgS f g s r k ix = (Alg f s r k ix, Alg g s r k ix)

type instance Alg (f :*: g) = AlgP f g
type AlgP f g s r k ix = Alg f s r (Alg g s r k) ix

type instance Alg (f :>: xi) = AlgT f xi
type AlgT f xi s r k ix = Alg f s r k xi

type Algebra s r = forall ix. Ix s ix => s ix -> Alg (PF s) s r r ix

class Fold (f :: (* -> *) -> (* -> *) -> * -> *) where
  alg :: (Ix s ix) => s ix -> Alg f s r k ix -> f s r ix -> k ix

instance Fold (K a) where
  alg _ f (K x) = f x

instance Fold (I xi) where
  alg _ f (I x) = f x

instance (Fold f, Fold g) => Fold (f :+: g) where
  alg _ (f, g) (L x) = alg index f x
  alg _ (f, g) (R x) = alg index g x

instance (Fold f, Fold g) => Fold (f :*: g) where
  alg _ f (x :*: y) = alg index (alg index f x) y

instance (Fold f) => Fold (f :>: xi) where
  alg _ f (Tag x) = alg index f x

fold :: forall s ix r . (Ix s ix, HFunctor (PF s), Fold (PF s)) =>
        Algebra s r ->
        ix -> r ix
fold f = alg (index :: s ix) (f index) . hmap (\ _ (I0 x) -> fold f x) . from

infixr 5 &
(&) :: a -> b -> (a, b)
(&) = (,)
