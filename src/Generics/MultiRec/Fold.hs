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
-- The definition of generic fold, unfold, paramorphisms. In addition,
-- some combinators that facilitate the construction of algebras.
--
-----------------------------------------------------------------------------

module Generics.MultiRec.Fold where

import Generics.MultiRec.Base
import Generics.MultiRec.HFunctor

import Control.Monad hiding (foldM)
import Control.Applicative

-- * Generic fold and unfold

type Algebra'  s f   r = forall ix. Ix s ix => s ix -> f s r ix -> r ix
type Algebra   s     r = Algebra' s (PF s) r
type AlgebraF' s f g r = forall ix. Ix s ix => s ix -> f s r ix -> g (r ix)
type AlgebraF  s   g r = AlgebraF' s (PF s) g r

fold :: (Ix s ix, HFunctor (PF s)) =>
        Algebra s r -> ix -> r ix
fold f = f index . hmap (\ _ (I0 x) -> fold f x) . from

foldM :: (Ix s ix, HFunctor (PF s), Monad m) =>
         AlgebraF s m r -> ix -> m (r ix)
foldM f x = hmapM (\ _ (I0 x) -> foldM f x) (from x) >>= f index

type CoAlgebra'  s f   r = forall ix. Ix s ix => s ix -> r ix -> f s r ix
type CoAlgebra   s     r = CoAlgebra' s (PF s) r
type CoAlgebraF' s f g r = forall ix. Ix s ix => s ix -> r ix -> g (f s r ix)
type CoAlgebraF  s   g r = CoAlgebraF' s (PF s) g r

unfold :: (Ix s ix, HFunctor (PF s)) =>
          CoAlgebra s r -> r ix -> ix
unfold f = to . hmap (\ _ x -> I0 (unfold f x)) . f index

unfoldM :: (Ix s ix, HFunctor (PF s), Monad m) =>
           CoAlgebraF s m r -> r ix -> m ix
unfoldM f x = f index x >>= liftM to . hmapM (\ _ x -> liftM I0 (unfoldM f x))

type ParaAlgebra'  s f   r = forall ix. Ix s ix => s ix -> f s r ix -> ix -> r ix
type ParaAlgebra   s     r = ParaAlgebra' s (PF s) r
type ParaAlgebraF' s f g r = forall ix. Ix s ix => s ix -> f s r ix -> ix -> g (r ix)
type ParaAlgebraF  s   g r = ParaAlgebraF' s (PF s) g r

para :: (Ix s ix, HFunctor (PF s)) => 
        ParaAlgebra s r -> ix -> r ix
para f x = f index (hmap (\ _ (I0 x) -> para f x) (from x)) x

paraM :: (Ix s ix, HFunctor (PF s), Monad m) => 
         ParaAlgebraF s m r -> ix -> m (r ix)
paraM f x = hmapM (\ _ (I0 x) -> paraM f x) (from x) >>= \ r -> f index r x

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

con :: AlgPart a s r ix -> AlgPart (C c a) s r ix
con f (C x) = f x

