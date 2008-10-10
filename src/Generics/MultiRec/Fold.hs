{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE TypeOperators       #-}
{-# LANGUAGE KindSignatures      #-}
{-# LANGUAGE LiberalTypeSynonyms #-}
{-# LANGUAGE GADTs               #-}

-----------------------------------------------------------------------------
-- |
-- Module      :  Generics.MultiRec.Fold
-- Copyright   :  (c) 2008 Universiteit Utrecht
-- License     :  BSD3
--
-- Maintainer  :  generics@haskell.org
-- Stability   :  experimental
-- Portability :  non-portable
--
-- The definition of generic fold.
--
-----------------------------------------------------------------------------

module Generics.MultiRec.Fold where

import Generics.MultiRec.Base
import Generics.MultiRec.HFunctor

-- * Generic fold and unfold

type Algebra s r = forall ix. Ix s ix => s ix -> PF s s r ix -> r ix

fold :: (Ix s ix, HFunctor (PF s)) =>
        Algebra s r -> ix -> r ix
fold f = f index . hmap (\ _ (I0 x) -> fold f x) . from

type CoAlgebra s r = forall ix. Ix s ix => s ix -> r ix -> PF s s r ix

unfold :: (Ix s ix, HFunctor (PF s)) =>
          CoAlgebra s r -> r ix -> ix
unfold f = to . hmap (\ _ x -> I0 (unfold f x)) . f index

type ParaAlgebra s r = forall ix. Ix s ix => s ix -> PF s s r ix -> ix -> r ix

para :: (Ix s ix, HFunctor (PF s)) => 
        ParaAlgebra s r -> ix -> r ix
para f x = f index (hmap (\ _ (I0 x) -> para f x) (from x)) x


-- * Creating an algebra

infixr 5 &
infixr :->

type AlgPart a (s :: * -> *) r ix = a s r ix -> r ix
type (f :-> g) (s :: * -> *) (r :: * -> *) ix = f s r ix -> g s r ix

(&) :: (AlgPart a :-> AlgPart b :-> AlgPart (a :+: b)) s r ix
(f & g) (L x) = f x
(f & g) (R x) = g x 

tag :: AlgPart a s r ix -> AlgPart (a :>: ix) s r ix'
tag f (Tag x) = f x

