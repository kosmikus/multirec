{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes       #-}
{-# LANGUAGE TypeOperators    #-}

-----------------------------------------------------------------------------
-- |
-- Module      :  Generics.MultiRec.Show
-- Copyright   :  (c) 2008 Universiteit Utrecht
-- License     :  BSD3
--
-- Maintainer  :  generics@haskell.org
-- Stability   :  experimental
-- Portability :  non-portable
--
-- Generic show.
--
-----------------------------------------------------------------------------

module Generics.MultiRec.Show where

import Generics.MultiRec.Base
import Generics.MultiRec.HFunctor
import Generics.MultiRec.Fold

import qualified Prelude as P
import Prelude hiding (show, showsPrec)

-- * Generic show

class HFunctor f => HShow f where
  hShowsPrecAlg :: Algebra' s f (K0 [Int -> ShowS])

instance HShow (I xi) where
  hShowsPrecAlg _ (I (K0 x)) = K0 x

-- | For constant types, we make use of the standard
-- show function.
instance Show x => HShow (K x) where
  hShowsPrecAlg _ (K x) = K0 [\ n -> P.showsPrec n x]

instance (HShow f, HShow g) => HShow (f :+: g) where
  hShowsPrecAlg ix (L x) = hShowsPrecAlg ix x
  hShowsPrecAlg ix (R y) = hShowsPrecAlg ix y

instance (HShow f, HShow g) => HShow (f :*: g) where
  hShowsPrecAlg ix (x :*: y) = K0 (unK0 (hShowsPrecAlg ix x) ++ unK0 (hShowsPrecAlg ix y))

instance HShow f => HShow (f :>: ix) where
  hShowsPrecAlg ix (Tag x) = hShowsPrecAlg ix x

instance HShow f => HShow (C c f) where
  hShowsPrecAlg ix cx@(C x) =
    case conFixity cx of
      Prefix    -> K0 [\ n -> showParen (not (null fields) && n > 10)
                                        (spaces ((conName cx ++) : map ($ 11) fields))]
      Infix a p -> K0 [\ n -> showParen (n > p)
                                        (spaces (head fields p : (conName cx ++) : map ($ p) (tail fields)))]
   where
    fields = unK0 $ hShowsPrecAlg ix x

-- | A variant of the algebra that takes an extra argument
-- to fix the system 's' the algebra works on.
hShowsPrecAlg_ :: (HShow f) => s ix -> Algebra' s f (K0 [Int -> ShowS])
hShowsPrecAlg_ _ = hShowsPrecAlg 

showsPrec :: forall s ix. (Ix s ix, HShow (PF s)) => s ix -> Int -> ix -> ShowS
showsPrec ix n x = spaces (map ($ n) (unK0 (fold (hShowsPrecAlg_ ix) x)))

show :: forall s ix. (Ix s ix, HShow (PF s)) => s ix -> ix -> String
show ix x = showsPrec ix 0 x ""

-- * Utilities

spaces :: [ShowS] -> ShowS
spaces []     = id
spaces [x]    = x
spaces (x:xs) = x . (' ':) . spaces xs
