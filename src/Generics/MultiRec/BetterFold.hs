{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE KindSignatures        #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE LiberalTypeSynonyms   #-}
{-# LANGUAGE Rank2Types            #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FlexibleInstances #-}

module Generics.MultiRec.BetterFold where

import Generics.MultiRec.Base
import Generics.MultiRec.HFunctor

type family Alg (f :: (* -> *) -> (* -> *) -> * -> *) 
                (s :: * -> *)      -- system
                (r :: * -> *)      -- recursive positions
                (ix :: *)          -- index
                :: *

type instance Alg (K a) (s :: * -> *) (r :: * -> *) ix = a -> r ix

type instance Alg U (s :: * -> *) (r :: * -> *) ix = r ix

type instance Alg (I xi) (s :: * -> *) r ix = r xi -> r ix

type instance Alg (f :+: g) s r ix = (Alg f s r ix, Alg g s r ix)

type instance Alg (K a :*: g) s r ix = a -> Alg g s r ix

type instance Alg (I xi :*: g) s r ix = r xi -> Alg g s r ix

type instance Alg (f :>: xi) s r ix = Alg f s r xi

type instance Alg (C c f) s r ix = Alg f s r ix

type Algebra s r = forall ix. Ix s ix => s ix -> Alg (PF s) s r ix

class Fold (f :: (* -> *) -> (* -> *) -> * -> *) where
  alg :: (Ix s ix) => Alg f s r ix -> f s r ix -> r ix

instance Fold (K a) where
  alg f (K x) = f x

instance Fold U where
  alg f U     = f

instance Fold (I xi) where
  alg f (I x) = f x

instance (Fold f, Fold g) => Fold (f :+: g) where
  alg (f, g) (L x) = alg f x
  alg (f, g) (R x) = alg g x

instance (Fold g) => Fold (K a :*: g) where
  alg f (K x :*: y) = alg (f x) y

instance (Fold g) => Fold (I xi :*: g) where
  alg f (I x :*: y) = alg (f x) y

instance (Fold f) => Fold (f :>: xi) where
  alg f (Tag x) = alg f x

instance (Fold f) => Fold (C c f) where
  alg f (C x) = alg f x

fold' :: forall s ix r . (Ix s ix, HFunctor (PF s), Fold (PF s)) =>
         s ix ->
         Algebra s r ->
         ix -> r ix
fold' ix f = (alg :: Alg (PF s) s r ix -> (PF s) s r ix -> r ix) (f ix) .
             hmap (\ _ (I0 x) -> fold' index f x) .
             from

fold :: forall s ix r . (Ix s ix, HFunctor (PF s), Fold (PF s)) =>
        Algebra s r ->
        ix -> r ix
fold = fold' index

infixr 5 &
(&) :: a -> b -> (a, b)
(&) = (,)
