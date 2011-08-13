{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE Rank2Types            #-}
{-# LANGUAGE KindSignatures        #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE PatternSignatures     #-}

-----------------------------------------------------------------------------
-- |
-- Module      :  Generics.MultiRec.Read
-- Copyright   :  (c) 2009--2010 Universiteit Utrecht
-- License     :  BSD3
--
-- Maintainer  :  generics@haskell.org
-- Stability   :  experimental
-- Portability :  non-portable
--
-- Generic read.
--
-----------------------------------------------------------------------------
module Generics.MultiRec.Read where

import Generics.MultiRec.Base

import Control.Monad
import Data.Char
import Data.Traversable
import Text.ParserCombinators.ReadP (char, skipSpaces, sepBy)
import Text.Read hiding (readsPrec, readPrec)
import Prelude hiding (readsPrec)
import qualified Prelude as P (readsPrec)


-- Based on Rui Barbosa's solution.


-- Count the number of terms in a product

class CountAtoms (f :: (* -> *) -> * -> *) where
  countatoms :: f r ix -> Int

instance CountAtoms (K a) where
  countatoms _ = 1

instance CountAtoms (I xi) where
  countatoms _ = 1

instance (CountAtoms f, CountAtoms g) => CountAtoms (f :*: g) where
  countatoms (_ :: (f :*: g) r ix) = countatoms (undefined :: f r ix) + countatoms (undefined :: g r ix)

-- * Generic read

class HReadPrec (phi :: * -> *) (f :: (* -> *) -> * -> *) where
   hreader :: forall ix . phi ix -> (forall ix1 . phi ix1 -> ReadPrec (I0 ix1)) -> ReadPrec (f I0 ix)


instance HReadPrec phi U where
   hreader p f = return U

instance (Read a) => HReadPrec phi (K a) where
   hreader p f = liftM K (readS_to_Prec P.readsPrec)

instance (El phi xi) => HReadPrec phi (I xi) where
   hreader p f = liftM I (f proof)

instance (HReadPrec phi f, HReadPrec phi g) => HReadPrec phi (f :+: g) where
   hreader p f = liftM L (hreader p f)  +++ liftM R (hreader p f)

instance (HReadPrec phi f, HReadPrec phi g) => HReadPrec phi (f :*: g) where
   hreader p f = liftM2 (:*:) (hreader p f) (hreader p f)

instance (HReadPrec phi f, EqS phi, El phi ix) => HReadPrec phi (f :>: ix) where
   hreader p f = case eqS p (proof :: phi ix) of
                       Nothing    ->  pfail
                       Just Refl  ->  liftM Tag (hreader p f)

instance (Read1 f, HReadPrec phi g) => HReadPrec phi (f :.: g) where
   hreader p f = liftM D (read1 (hreader p f))

class Read1 f where
  read1 :: ReadPrec (g I0 ix) -> ReadPrec (f (g I0 ix))

instance Read1 [] where
  read1 pe = do
    Punc "[" <- lexP
    xs <- lift $ sepBy (readPrec_to_P pe 0)
                       (readPrec_to_P (do Punc "," <- lexP; return ()) 0)
    Punc "]" <- lexP
    return xs

instance Read1 Maybe where
  read1 pe =
    (readNoArgsCons "Nothing" >> return Nothing) +++
    (liftM Just $ readPrefixCons pe True "Just")

-- Dealing with constructors

-- No arguments
instance (Constructor c) => HReadPrec phi (C c U) where
   hreader p f = let constr = undefined :: C c U I0 ix
                     name   = conName constr
                 in readCons (readNoArgsCons name)

-- 1 argument
instance (Constructor c, HReadPrec phi (I xi)) => HReadPrec phi (C c (I xi)) where
   hreader p f = let constr = undefined :: C c (I xi) I0 ix
                     name   = conName constr
                 in  readCons (readPrefixCons (hreader p f) True name)

instance (Constructor c, HReadPrec phi (K a)) => HReadPrec phi (C c (K a)) where
   hreader p f = let constr = undefined :: C c (K a) I0 ix
                     name   = conName constr
                 in  readCons (readPrefixCons (hreader p f) True name)

instance (Constructor c, HReadPrec phi (f :.: g)) => HReadPrec phi (C c (f :.: g)) where
   hreader p f = let constr = undefined :: C c (f :.: g) I0 ix
                     name   = conName constr
                 in  readCons (readPrefixCons (hreader p f) True name)

-- 2 arguments or more
instance forall f g phi c . (Constructor c, CountAtoms (f :*: g), HReadPrec phi f , HReadPrec phi g) => HReadPrec phi (C c (f:*:g)) where
   hreader p f = let constr = undefined :: C c (f:*:g) I0 ix
                     name   = conName constr
                     fixity = conFixity constr
                     (assoc,prc,isInfix) = case fixity of
                                            Prefix      -> (LeftAssociative, 9, False)
                                            Infix a p   -> (a, p, True)
                     --K0F nargs  = countatoms  :: K0F Int (f:*:g)
                     nargs  = countatoms (undefined :: (f :*: g) r ix)
                  in   readCons $
                               readPrefixCons (hreader p f) (not isInfix) name
                                        +++
                               (do guard (nargs==2)
                                   readInfixCons p f (assoc,prc,isInfix) name
                               )


readCons :: (Constructor c) => ReadPrec (f I0 ix) -> ReadPrec (C c f I0 ix)
readCons = liftM C

readPrefixCons :: ReadPrec (f I0 ix)
                  -> Bool -> String -> ReadPrec (f I0 ix)
readPrefixCons pe b name  = parens . prec appPrec $
                            do parens (prefixConsNm name b)
                               step pe
    where prefixConsNm name True  = do Ident n <- lexP
                                       guard (name == n)
          prefixConsNm name False = do Punc "(" <-lexP
                                       Symbol n <- lexP
                                       guard (name==n)
                                       Punc ")" <- lexP
                                       return ()


readInfixCons :: (HReadPrec phi f, HReadPrec phi g) =>
                    phi ix
                 -> (forall ix1. phi ix1 -> ReadPrec (I0 ix1))
                 -> (Associativity,Int,Bool) -> String -> ReadPrec ((f :*: g) I0 ix)
readInfixCons p f (asc,prc,b) name = parens . prec prc $
                                       do x <- {- (if asc == LeftAssociative  then id else step) -} step (hreader p f)
                                          parens (infixConsNm name b)
                                          y <- (if asc == RightAssociative then id else step) (hreader p f)
                                          return  (x :*: y)
     where  infixConsNm name True  = do Symbol n <- lexP
                                        guard (n==name)
            infixConsNm name False = do Punc "`"  <- lexP
                                        Ident n   <- lexP
                                        guard (n==name)
                                        Punc "`"  <- lexP
                                        return ()

readNoArgsCons :: String -> ReadPrec (U I0 ix)
readNoArgsCons name = parens $
                      do Ident n <- lexP
                         guard (n==name)
                         return U

appPrec :: Int
appPrec = 10


-- Exported functions

readPrec :: (Fam phi, HReadPrec phi (PF phi)) => phi ix -> ReadPrec ix
readPrec p = liftM (to p)  (hreader p (liftM I0 . readPrec))


readsPrec :: (Fam phi, HReadPrec phi (PF phi)) => phi ix -> Int -> ReadS ix
readsPrec = readPrec_to_S . readPrec

read :: (Fam phi, HReadPrec phi (PF phi)) => phi ix -> String -> ix
read p s = case [x |  (x,remain) <- readsPrec p 0 s , all isSpace remain] of
               [x] -> x
               [ ] -> error "no parse"
               _   -> error "ambiguous parse"
