{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE TypeOperators       #-}
{-# LANGUAGE KindSignatures      #-}
{-# LANGUAGE LiberalTypeSynonyms #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE TypeFamilies        #-}

-----------------------------------------------------------------------------
-- |
-- Module      :  Generics.MultiRec.FoldK
-- Copyright   :  (c) 2009 Universiteit Utrecht
-- License     :  BSD3
--
-- Maintainer  :  generics@haskell.org
-- Stability   :  experimental
-- Portability :  non-portable
--
-- Variant of "Generics.MultiRec.Fold" where the result type is independent of
-- the index.
--
-----------------------------------------------------------------------------

module Generics.MultiRec.FoldK where

import Generics.MultiRec.Base
import Generics.MultiRec.HFunctor

import Control.Monad hiding (foldM)
import Control.Applicative

-- * Generic fold and unfold

type Algebra'  s f   r = forall ix. Ix s ix => s ix -> f s (K0 r) ix -> r
type Algebra   s     r = Algebra' s (PF s) r
type AlgebraF' s f g r = forall ix. Ix s ix => s ix -> f s (K0 r) ix -> g r
type AlgebraF  s   g r = AlgebraF' s (PF s) g r

fold :: (Ix s ix, HFunctor (PF s)) =>
        Algebra s r -> ix -> r
fold f = f index . hmap (\ _ (I0 x) -> K0 (fold f x)) . from

foldM :: (Ix s ix, HFunctor (PF s), Monad m) =>
         AlgebraF s m r -> ix -> m r
foldM f x = hmapM (\ _ (I0 x) -> liftM K0 (foldM f x)) (from x) >>= f index

type CoAlgebra'  s f   r = forall ix. Ix s ix => s ix -> r -> f s (K0 r) ix
type CoAlgebra   s     r = CoAlgebra' s (PF s) r
type CoAlgebraF' s f g r = forall ix. Ix s ix => s ix -> r -> g (f s (K0 r) ix)
type CoAlgebraF  s   g r = CoAlgebraF' s (PF s) g r

unfold :: (Ix s ix, HFunctor (PF s)) =>
          CoAlgebra s r -> r -> ix
unfold f = to . hmap (\ _ (K0 x) -> I0 (unfold f x)) . f index

unfoldM :: (Ix s ix, HFunctor (PF s), Monad m) =>
           CoAlgebraF s m r -> r -> m ix
unfoldM f x = f index x >>= liftMto . hmapM (\ _ (K0 x) -> liftM I0 (unfoldM f x))
  where
    -- only for ghc-6.8.3 compatibility
    liftMto :: (Monad m, Ix s ix, pfs ~ PF s) => m (pfs s I0 ix) -> m ix
    liftMto = liftM to

type ParaAlgebra'  s f   r = forall ix. Ix s ix => s ix -> f s (K0 r) ix -> ix -> r
type ParaAlgebra   s     r = ParaAlgebra' s (PF s) r
type ParaAlgebraF' s f g r = forall ix. Ix s ix => s ix -> f s (K0 r) ix -> ix -> g r
type ParaAlgebraF  s   g r = ParaAlgebraF' s (PF s) g r

para :: (Ix s ix, HFunctor (PF s)) => 
        ParaAlgebra s r -> ix -> r
para f x = f index (hmap (\ _ (I0 x) -> K0 (para f x)) (from x)) x

paraM :: (Ix s ix, HFunctor (PF s), Monad m) => 
         ParaAlgebraF s m r -> ix -> m r
paraM f x = hmapM (\ _ (I0 x) -> liftM K0 (paraM f x)) (from x) >>= \ r -> f index r x

-- * Creating an algebra

infixr 5 &
infixr :->

type AlgPart a (s :: * -> *) b ix = a s (K0 b) ix -> b
type (f :-> g) (s :: * -> *) b ix = f s b ix -> g s b ix

(&) :: (AlgPart a :-> AlgPart b :-> AlgPart (a :+: b)) s c ix
(f & g) (L x) = f x
(f & g) (R x) = g x 

tag :: AlgPart a s c ix -> AlgPart (a :>: ix) s c ix'
tag f (Tag x) = f x

con :: AlgPart a s b ix -> AlgPart (C c a) s b ix
con f (C x) = f x
