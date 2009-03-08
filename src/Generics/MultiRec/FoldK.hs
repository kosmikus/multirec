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

type Algebra'  phi f   r = forall ix. phi ix -> f (K0 r) ix -> r
type Algebra   phi     r = Algebra' phi (PF phi) r
type AlgebraF' phi f g r = forall ix. phi ix -> f (K0 r) ix -> g r
type AlgebraF  phi   g r = AlgebraF' phi (PF phi) g r

fold :: (Fam phi, HFunctor phi (PF phi)) =>
        Algebra phi r -> phi ix -> ix -> r
fold f p = f p . hmap (\ p (I0 x) -> K0 (fold f p x)) . from p

foldM :: (Fam phi, HFunctor phi (PF phi), Monad m) =>
         AlgebraF phi m r -> phi ix -> ix -> m r
foldM f p x = hmapM (\ p (I0 x) -> liftM K0 (foldM f p x)) (from p x) >>= f p

type CoAlgebra'  phi f   r = forall ix. phi ix -> r -> f (K0 r) ix
type CoAlgebra   phi     r = CoAlgebra' phi (PF phi) r
type CoAlgebraF' phi f g r = forall ix. phi ix -> r -> g (f (K0 r) ix)
type CoAlgebraF  phi   g r = CoAlgebraF' phi (PF phi) g r

unfold :: (Fam phi, HFunctor phi (PF phi)) =>
          CoAlgebra phi r -> phi ix -> r -> ix
unfold f p = to p . hmap (\ p (K0 x) -> I0 (unfold f p x)) . f p

unfoldM :: (Fam phi, HFunctor phi (PF phi), Monad m) =>
           CoAlgebraF phi m r -> phi ix -> r -> m ix
unfoldM f p x = f p x >>= liftM (to p) . hmapM (\ p (K0 x) -> liftM I0 (unfoldM f p x))

type ParaAlgebra'  phi f   r = forall ix. phi ix -> f (K0 r) ix -> ix -> r
type ParaAlgebra   phi     r = ParaAlgebra' phi (PF phi) r
type ParaAlgebraF' phi f g r = forall ix. phi ix -> f (K0 r) ix -> ix -> g r
type ParaAlgebraF  phi   g r = ParaAlgebraF' phi (PF phi) g r

para :: (Fam phi, HFunctor phi (PF phi)) => 
        ParaAlgebra phi r -> phi ix -> ix -> r
para f p x = f p (hmap (\ p (I0 x) -> K0 (para f p x)) (from p x)) x

paraM :: (Fam phi, HFunctor phi (PF phi), Monad m) => 
         ParaAlgebraF phi m r -> phi ix -> ix -> m r
paraM f p x = hmapM (\ p (I0 x) -> liftM K0 (paraM f p x)) (from p x) >>= \ r -> f p r x

-- * Creating an algebra

infixr 5 &
infixr :->

type AlgPart f b ix = f (K0 b) ix -> b
type (f :-> g) b ix = f b ix -> g b ix

(&) :: (AlgPart a :-> AlgPart b :-> AlgPart (a :+: b)) c ix
(f & g) (L x) = f x
(f & g) (R x) = g x 

tag :: AlgPart a c ix -> AlgPart (a :>: ix) c ix'
tag f (Tag x) = f x

con :: AlgPart a b ix -> AlgPart (C c a) b ix
con f (C x) = f x
