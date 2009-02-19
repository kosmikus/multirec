{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE TypeOperators       #-}
{-# LANGUAGE KindSignatures      #-}
{-# LANGUAGE LiberalTypeSynonyms #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE TypeFamilies        #-}

-----------------------------------------------------------------------------
-- |
-- Module      :  Generics.MultiRec.Fold
-- Copyright   :  (c) 2008--2009 Universiteit Utrecht
-- License     :  BSD3
--
-- Maintainer  :  generics@haskell.org
-- Stability   :  experimental
-- Portability :  non-portable
--
-- The definition of generic fold, unfold, paramorphisms. In addition,
-- some combinators that facilitate the construction of algebras.
--
-- There are several variants of fold in other modules that are probably
-- easier to use:
--
--   * for folds with constant return type, look at 
--     "Generics.MultiRec.FoldAlgK" (or "Generics.MultiRec.FoldK"),
--
--   * for other folds, look at "Generics.MultiRec.FoldAlg".
--
-----------------------------------------------------------------------------

module Generics.MultiRec.Fold where

import Generics.MultiRec.Base
import Generics.MultiRec.HFunctor

import Control.Monad hiding (foldM)
import Control.Applicative

-- * Generic fold and unfold

type Algebra'  s es f   r = forall ix. Ix s es ix => s es ix -> f s es r ix -> r ix
type Algebra   s es     r = Algebra' s es (PF (s es)) r
type AlgebraF' s es f g r = forall ix. Ix s es ix => s es ix -> f s es r ix -> g (r ix)
type AlgebraF  s es   g r = AlgebraF' s es (PF (s es)) g r

fold :: (Ix s es ix, HFunctor (PF (s es))) =>
        Algebra s es r -> ix -> r ix
fold f = f index . hmap (\ _ (I0 x) -> fold f x) . from

foldM :: (Ix s es ix, HFunctor (PF (s es)), Monad m) =>
         AlgebraF s es m r -> ix -> m (r ix)
foldM f x = hmapM (\ _ (I0 x) -> foldM f x) (from x) >>= f index

type CoAlgebra'  s es f   r = forall ix. Ix s es ix => s es ix -> r ix -> f s es r ix
type CoAlgebra   s es     r = CoAlgebra' s es (PF (s es)) r
type CoAlgebraF' s es f g r = forall ix. Ix s es ix => s es ix -> r ix -> g (f s es r ix)
type CoAlgebraF  s es   g r = CoAlgebraF' s es (PF (s es)) g r

unfold :: (Ix s es ix, HFunctor (PF (s es))) =>
          CoAlgebra s es r -> r ix -> ix
unfold f = to . hmap (\ _ x -> I0 (unfold f x)) . f index

unfoldM :: (Ix s es ix, HFunctor (PF (s es)), Monad m) =>
           CoAlgebraF s es m r -> r ix -> m ix
unfoldM f x = f index x >>= liftMto . hmapM (\ _ x -> liftM I0 (unfoldM f x))
  where
    -- only for ghc-6.8.3 compatibility
    liftMto :: (Monad m, Ix s es ix, pfs ~ PF (s es)) => m (pfs s es I0 ix) -> m ix
    liftMto = liftM to

type ParaAlgebra'  s es f   r = forall ix. Ix s es ix => s es ix -> f s es r ix -> ix -> r ix
type ParaAlgebra   s es     r = ParaAlgebra' s es (PF (s es)) r
type ParaAlgebraF' s es f g r = forall ix. Ix s es ix => s es ix -> f s es r ix -> ix -> g (r ix)
type ParaAlgebraF  s es   g r = ParaAlgebraF' s es (PF (s es)) g r

para :: (Ix s es ix, HFunctor (PF (s es))) => 
        ParaAlgebra s es r -> ix -> r ix
para f x = f index (hmap (\ _ (I0 x) -> para f x) (from x)) x

paraM :: (Ix s es ix, HFunctor (PF (s es)), Monad m) => 
         ParaAlgebraF s es m r -> ix -> m (r ix)
paraM f x = hmapM (\ _ (I0 x) -> paraM f x) (from x) >>= \ r -> f index r x

-- * Creating an algebra

infixr 5 &
infixr :->

type AlgPart a (s :: (* -> *) -> * -> *) (es :: * -> *) r ix = a s es r ix -> r ix
type (f :-> g) (s :: (* -> *) -> * -> *) (es :: * -> *) (r :: * -> *) ix = f s es r ix -> g s es r ix

(&) :: (AlgPart a :-> AlgPart b :-> AlgPart (a :+: b)) s es r ix
(f & g) (L x) = f x
(f & g) (R x) = g x 

tag :: AlgPart a s es r ix -> AlgPart (a :>: ix) s es r ix'
tag f (Tag x) = f x

con :: AlgPart a s es r ix -> AlgPart (C c a) s es r ix
con f (C x) = f x
