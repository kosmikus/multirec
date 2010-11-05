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
-- Copyright   :  (c) 2008--2010 Universiteit Utrecht
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
--   * for folds with convenient algebras, look at
--     "Generics.MultiRec.FoldAlg".
--
-----------------------------------------------------------------------------

module Generics.MultiRec.Fold where

import Generics.MultiRec.Base
import Generics.MultiRec.HFunctor

import Control.Monad hiding (foldM)
import Control.Applicative

-- * Generic fold and unfold

type Algebra'  phi f   r = forall ix. phi ix -> f r ix -> r ix
type Algebra   phi     r = Algebra' phi (PF phi) r
type AlgebraF' phi f g r = forall ix. phi ix -> f r ix -> g (r ix)
type AlgebraF  phi   g r = AlgebraF' phi (PF phi) g r

fold :: (Fam phi, HFunctor phi (PF phi)) =>
        Algebra phi r -> phi ix -> ix -> r ix
fold f p = f p . hmap (\ p (I0 x) -> fold f p x) p . from p

foldM :: (Fam phi, HFunctor phi (PF phi), Monad m) =>
         AlgebraF phi m r -> phi ix -> ix -> m (r ix)
foldM f p x = hmapM (\ p (I0 x) -> foldM f p x) p (from p x) >>= f p

type CoAlgebra'  phi f   r = forall ix. phi ix -> r ix -> f r ix
type CoAlgebra   phi     r = CoAlgebra' phi (PF phi) r
type CoAlgebraF' phi f g r = forall ix. phi ix -> r ix -> g (f r ix)
type CoAlgebraF  phi   g r = CoAlgebraF' phi (PF phi) g r

unfold :: (Fam phi, HFunctor phi (PF phi)) =>
          CoAlgebra phi r -> phi ix -> r ix -> ix
unfold f p = to p . hmap (\ p x -> I0 (unfold f p x)) p . f p

unfoldM :: (Fam phi, HFunctor phi (PF phi), Monad m) =>
           CoAlgebraF phi m r -> phi ix -> r ix -> m ix
unfoldM f p x = f p x >>= liftM (to p) . hmapM (\ p x -> liftM I0 (unfoldM f p x)) p

type ParaAlgebra'  phi f   r = forall ix. phi ix -> f r ix -> ix -> r ix
type ParaAlgebra   phi     r = ParaAlgebra' phi (PF phi) r
type ParaAlgebraF' phi f g r = forall ix. phi ix -> f r ix -> ix -> g (r ix)
type ParaAlgebraF  phi   g r = ParaAlgebraF' phi (PF phi) g r

para :: (Fam phi, HFunctor phi (PF phi)) => 
        ParaAlgebra phi r -> phi ix -> ix -> r ix
para f p x = f p (hmap (\ p (I0 x) -> para f p x) p (from p x)) x

paraM :: (Fam phi, HFunctor phi (PF phi), Monad m) => 
         ParaAlgebraF phi m r -> phi ix -> ix -> m (r ix)
paraM f p x = hmapM (\ p (I0 x) -> paraM f p x) p (from p x) >>= \ r -> f p r x

-- * Creating an algebra

infixr 5 &
infixr :->

type AlgPart f r ix = f r ix -> r ix
type (f :-> g) (r :: * -> *) ix = f r ix -> g r ix

(&) :: (AlgPart a :-> AlgPart b :-> AlgPart (a :+: b)) r ix
(f & g) (L x) = f x
(f & g) (R x) = g x 

tag :: AlgPart a r ix -> AlgPart (a :>: ix) r ix'
tag f (Tag x) = f x

con :: AlgPart a r ix -> AlgPart (C c a) r ix
con f (C x) = f x

