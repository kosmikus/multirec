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
-- Variant of Generics.MultiRec.Fold where the result type is independent of
-- the index.
--
-----------------------------------------------------------------------------

module Generics.MultiRec.FoldK where

import Generics.MultiRec.Base
import Generics.MultiRec.HFunctor

import Control.Monad hiding (foldM)
import Control.Applicative

-- * Generic fold and unfold

type Algebra' s f   a = forall ix. Ix s ix => s ix -> f s (K0 a) ix -> a
type Algebra  s     a = Algebra' s (PF s) a

fold :: (Ix s ix, HFunctor (PF s)) =>
        Algebra s a -> ix -> a
fold f = f index . hmap (\ _ (I0 x) -> K0 (fold f x)) . from

{-
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
unfoldM f x = f index x >>= liftMto . hmapM (\ _ x -> liftM I0 (unfoldM f x))
  where
    -- only for ghc-6.8.3 compatibility
    liftMto :: (Monad m, Ix s ix, pfs ~ PF s) => m (pfs s I0 ix) -> m ix
    liftMto = liftM to

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
-}

-- * Creating an algebra

infixr 5 &
infixr :->

type AlgPart a (s :: * -> *) b ix = a s (K0 b) ix -> b
type (f :-> g) (s :: * -> *) b ix = f s b ix -> g s b ix

(&) :: (AlgPart a :-> AlgPart b :-> AlgPart (a :+: b)) s c ix
(f & g) (L x) = f x
(f & g) (R x) = g x 


