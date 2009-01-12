{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE KindSignatures        #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE LiberalTypeSynonyms   #-}
{-# LANGUAGE Rank2Types            #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FlexibleInstances #-}

module Generics.MultiRec.BetterFoldK where

import Generics.MultiRec.Base
import Generics.MultiRec.HFunctor

type family Alg (f :: (* -> *) -> (* -> *) -> * -> *) 
                (s :: * -> *)      -- system
                (r :: *)           -- result type
                :: *

type instance Alg (K a) (s :: * -> *) r = a -> r

type instance Alg U (s :: * -> *) r = r

type instance Alg (I xi) (s :: * -> *) r = r -> r

type instance Alg (f :+: g) s r = (Alg f s r, Alg g s r)

type instance Alg (K a :*: g) s r = a -> Alg g s r

type instance Alg (I xi :*: g) s r = r -> Alg g s r

type instance Alg (f :>: xi) s r = Alg f s r

type instance Alg (C c f) s r = Alg f s r

type Algebra s r = forall ix. Ix s ix => s ix -> Alg (PF s) s r

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

fold' :: forall s ix r . (Ix s ix, HFunctor (PF s), Fold (PF s)) =>
         s ix ->
         Algebra s r ->
         ix -> r
fold' ix f = (alg :: Alg (PF s) s r -> (PF s) s (K0 r) ix -> r) (f ix) .
             hmap (\ _ (I0 x) -> K0 (fold' index f x)) .
             from

fold :: forall s ix r . (Ix s ix, HFunctor (PF s), Fold (PF s)) =>
        Algebra s r ->
        ix -> r
fold = fold' index

infixr 5 &
(&) :: a -> b -> (a, b)
(&) = (,)
