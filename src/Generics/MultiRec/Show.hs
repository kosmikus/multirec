{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE UndecidableInstances  #-}

-----------------------------------------------------------------------------
-- |
-- Module      :  Generics.MultiRec.Show
-- Copyright   :  (c) 2008--2010 Universiteit Utrecht
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
import Generics.MultiRec.FoldK

import qualified Prelude as P
import Prelude hiding (show, showsPrec)
import Data.Traversable (Traversable(..))

-- * Generic show

-- | The list in the result type allows us to get at
-- the fields of a constructor individually, which in
-- turn allows us to insert additional stuff in between
-- if record notation is used.
class HFunctor phi f => HShow phi f where
  hShowsPrecAlg :: Algebra' phi f [Int -> ShowS]

instance El phi xi => HShow phi (I xi) where
  hShowsPrecAlg _ (I (K0 x)) = x

-- | For constant types, we make use of the standard
-- show function.
instance Show a => HShow phi (K a) where
  hShowsPrecAlg _ (K x) = [\ n -> P.showsPrec n x]

instance HShow phi U where
  hShowsPrecAlg _ U = []

instance (HShow phi f, HShow phi g) => HShow phi (f :+: g) where
  hShowsPrecAlg ix (L x) = hShowsPrecAlg ix x
  hShowsPrecAlg ix (R y) = hShowsPrecAlg ix y

instance (HShow phi f, HShow phi g) => HShow phi (f :*: g) where
  hShowsPrecAlg ix (x :*: y) = hShowsPrecAlg ix x ++ hShowsPrecAlg ix y

instance HShow phi f => HShow phi (f :>: ix) where
  hShowsPrecAlg ix (Tag x) = hShowsPrecAlg ix x

instance (Show1 f, Traversable f, HShow phi g) => HShow phi (f :.: g) where
  hShowsPrecAlg ix (D x) = [show1 (fmap (hShowsPrecAlg ix) x)]
 
instance (Constructor c, HShow phi f) => HShow phi (C c f) where
  hShowsPrecAlg ix cx@(C x) =
    case conFixity cx of
      Prefix    -> [\ n -> showParen (not (null fields) && n > 10)
                                     (spaces ((conName cx ++) : map ($ 11) fields))]
      Infix a p -> [\ n -> showParen (n > p)
                                     (spaces (head fields p : (conName cx ++) : map ($ p) (tail fields)))]
   where
    fields = hShowsPrecAlg ix x

class Show1 f where
  show1 :: f [Int -> ShowS] -> Int -> ShowS

instance Show1 Maybe where
  show1 Nothing  _ = ("Nothing" ++)
  show1 (Just x) n = showParen (n > 10) (spaces (("Just" ++) : map ($ 11) x))

instance Show1 [] where
  show1 [] _ = ("[]" ++)
  show1 xs _ = ('[':) . commas (map ($ 0) (concat xs)) . (']':)

showsPrec :: (Fam phi, HShow phi (PF phi)) => phi ix -> Int -> ix -> ShowS
showsPrec p n x = spaces (map ($ n) (fold hShowsPrecAlg p x))

show :: (Fam phi, HShow phi (PF phi)) => phi ix -> ix -> String
show ix x = showsPrec ix 0 x ""

-- * Utilities

spaces :: [ShowS] -> ShowS
spaces = intersperse " "

commas :: [ShowS] -> ShowS
commas = intersperse ", "

intersperse :: String -> [ShowS] -> ShowS
intersperse s []     = id
intersperse s [x]    = x
intersperse s (x:xs) = x . (s ++) . spaces xs

