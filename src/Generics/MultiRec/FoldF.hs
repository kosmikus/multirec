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

module Generics.MultiRec.FoldF where

import Generics.MultiRec.BaseF
import Generics.MultiRec.HFunctorF

-- * Generic fold and unfold

type Algebra s r = forall e ix. Ix s ix => s ix -> PF s s r e ix -> r e ix

fold :: (Ix s ix, HFunctor (PF s)) =>
        Algebra s r -> ix e -> r e ix
fold f = f index . hmap (\ _ (I0 x) -> fold f x) . from

type CoAlgebra s r = forall e ix. Ix s ix => s ix -> r e ix -> PF s s r e ix

unfold :: (Ix s ix, HFunctor (PF s)) =>
          CoAlgebra s r -> r e ix -> ix e
unfold f = to . hmap (\ _ x -> I0 (unfold f x)) . f index

type ParaAlgebra s r = forall e ix. Ix s ix => s ix -> PF s s r e ix -> ix e -> r e ix

para :: (Ix s ix, HFunctor (PF s)) => 
        ParaAlgebra s r -> ix e -> r e ix
para f x = f index (hmap (\ _ (I0 x) -> para f x) (from x)) x

-- * Creating an algebra

infixr 5 &
infixr :->

type AlgPart a (s :: (* -> *) -> *) r e (ix :: * -> *) = a s r e ix -> r e ix
type (f :-> g) (s :: (* -> *) -> *) (r :: * -> (* -> *) -> *) e (ix :: * -> *) = f s r e ix -> g s r e ix

(&) :: (AlgPart a :-> AlgPart b :-> AlgPart (a :+: b)) s r e ix
(f & g) (L x) = f x
(f & g) (R x) = g x 

tag :: AlgPart a s r e ix -> AlgPart (a :>: ix) s r e ix'
tag f (Tag x) = f x
