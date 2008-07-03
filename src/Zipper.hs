{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE StandaloneDeriving   #-}
{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE PatternSignatures    #-}
{-# LANGUAGE ScopedTypeVariables  #-}
{-# LANGUAGE GADTs                #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE EmptyDataDecls       #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE Rank2Types           #-}

module Zipper where

import Control.Monad

import Base

-- -----------------------------------------------------------------
-- Representation types for contexts
-- -----------------------------------------------------------------
-- ixh : type of hole
-- ix  : type of tree
data Prod' df f (l :: * -> *) ixh ix = Prod' (df l ixh ix) (f l ix)

data Sum' df dg (l :: * -> *) ixh ix = L' (df l ixh ix) | R' (dg l ixh ix)

data Zero' (l :: * -> *) ixh ix

data Tag' ixtag df (l :: * -> *) ixh ix where
  Tag' :: df l ixh ix -> Tag' ix df l ixh ix

data Unit' xi (l :: * -> *) ixh ix where
  Unit' :: Unit' ixh l ixh ix

type Unit = K ()

-- -----------------------------------------------------------------
-- Zipper datatype and high-level functions
-- -----------------------------------------------------------------
data Zipper l ix where
  Zipper :: Ix l ixh => ixh -> (CList l ixh ix) -> Zipper l ix

data CList l ixh ix where
  CNil  :: CList l ix ix
  CCons :: Ix l ix => D (PF l) l ixh ix -> CList l ix ix' -> CList l ixh ix' 

toZipper :: Ix l ix => ix -> Zipper l ix
toZipper x = Zipper x CNil

fromFirstF :: (ZipFuns (PF l),Ix l ixh) => ixh -> Maybe (ExFirst (PF l) l ixh)
fromFirstF = firstf . from

down :: forall l ix . (ZipFuns (PF l)) => Zipper l ix -> Maybe (Zipper l ix)
down (Zipper (x::ix') ctxs)
  = do
    ExFirst ctx x' <- (fromFirstF x::Maybe (ExFirst (PF l) l ix'))
    return (Zipper x' (CCons ctx ctxs))

applyZipper :: (forall ix . l ix -> ix -> a) -> Zipper l ix -> a
applyZipper f (Zipper x _) = f ix x

--up :: forall l ix . ZipFuns (PF l) => Zipper l ix -> Maybe (Zipper l ix)
--up (Zipper _ CNil) = Nothing
--up (Zipper (x::ixh) (CCons (ctx::D (PF l) l ixh ix') ctxs)) = undefined --Just (plugIt x ctx ctxs)--Just (Zipper (to (upf x ctx)) ctxs)
--  where
--    --plugIt :: forall l ix ixh ix' . (Ix l ix',ZipFuns (PF l))
--    --       => ixh -> D (PF l) l ixh ix'  -> CList l ix' ix -> Zipper l ix
--    --plugIt = ((Zipper . to) . ) . upf
--    test = upf x ctx :: Str l ix'
--    test2 :: forall l ix' ix . (Ix l ix', ZipFuns (PF l)) => Str l ix' -> CList l ix' ix -> Zipper l ix
--    test2 = Zipper . to

rev f g x = g (f (x))

o2 :: (a -> b -> c) -> (c -> d) -> (a -> b -> d)
o2 f g x y = g (f x y) 

o2' :: (a -> b) -> (b -> c -> d) -> (a -> c -> d)
o2' f g x y = g (f x) y

-- -----------------------------------------------------------------
-- D operator
-- -----------------------------------------------------------------
class Diff (f ::  (* -> *) -> * -> * ) where
  type D f :: (* -> *) -- family name
           -> *        -- type of the hole
           -> *        -- type of surrounding tree
           -> *

instance Diff (K a) where
  type D (K a) = Zero'

instance Diff (Id xi) where
  type D (Id xi) = Unit' xi

instance (Diff f, Diff g) => Diff (f :+: g) where
  type D (f :+: g) = D f `Sum'` D g

instance (Diff f, Diff g) => Diff (f :*: g) where
  type D (f :*: g) = Prod' (D f) g `Sum'` Prod' (D g) f

instance Diff f => Diff (f ::: ixtag) where
  type D (f ::: ixtag) = Tag' ixtag (D f)

data ExFirst f l ix = forall ixh . Ix l ixh => ExFirst (D f l ixh ix) ixh

-- -----------------------------------------------------------------
-- Zipper generic functions
-- -----------------------------------------------------------------
class ZipFuns (f :: (* -> *) -> * -> *) where
  firstf :: f l ix -> Maybe (ExFirst f l ix)
  upf    :: Ix l ixh => ixh -> D f l ixh ix -> f l ix
  --nextf  :: Ix l ixh => ixh -> D f ixh ix -> Either (ExFirst f l ix) (f l ix)

instance ZipFuns f => ZipFuns (f ::: ixtag) where
  firstf (Tag x)
   = do
     ExFirst ctx h <- firstf x
     return (ExFirst (Tag' ctx) h) 
  upf h (Tag' ctx) = Tag (upf h ctx)

instance (ZipFuns f, ZipFuns g) => ZipFuns (f :*: g) where
  firstf (x :*: y)
   = do
     ExFirst ctx h <- firstf x
     return (ExFirst (L' (Prod' ctx y)) h)
     `mplus`
     do
     ExFirst ctx h <- firstf y
     return (ExFirst (R' (Prod' ctx x)) h)
  upf h (L' (Prod' ctx y)) = upf h ctx :*: y
  upf h (R' (Prod' ctx x)) = x         :*: upf h ctx
  

instance ZipFuns (K a) where
  firstf (K _) = Nothing
  upf ixh zeroval = undefined

instance ZipFuns (Id xi) where
  firstf (Id x) = Just (ExFirst Unit' x)
  upf ixh Unit' = Id ixh

instance (ZipFuns f, ZipFuns g) => ZipFuns (f :+: g) where
  firstf (L x)
   = do
     ExFirst ctx h <- firstf x
     return (ExFirst (L' ctx) h)
  firstf (R x)
   = do
     ExFirst ctx h <- firstf x
     return (ExFirst (R' ctx) h)
  upf h (L' ctx) = L (upf h ctx)
  upf h (R' ctx) = R (upf h ctx)


