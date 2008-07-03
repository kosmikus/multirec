{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE StandaloneDeriving   #-}
{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE PatternSignatures    #-}
{-# LANGUAGE ScopedTypeVariables  #-}
{-# LANGUAGE GADTs                #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE EmptyDataDecls       #-}
{-# LANGUAGE TypeOperators        #-}

module Zipper where

import Control.Monad

import Base

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



data Zipper l ix where
  Zipper :: Ix l ixh => ixh -> (CList l ixh ix) -> Zipper l ix

data CList l ixh ix where
  CNil :: CList l ix ix
  CCons :: D (PF l) l ixh ix -> CList l ix ix' -> CList l ixh ix' 

toZipper :: Ix l ix => ix -> Zipper l ix
toZipper x = Zipper x CNil

fromFirstF :: (ZipFuns (PF l),Ix l ixh) => ixh -> Maybe (ExFirst (PF l) l ixh)
fromFirstF = firstf . from

down :: forall l ix . (ZipFuns (PF l)) => Zipper l ix -> Maybe (Zipper l ix)
down (Zipper (x::ix') ctxs)
  = do
    ExFirst ctx x' <- (fromFirstF x::Maybe (ExFirst (PF l) l ix'))
    return (Zipper x' (CCons ctx ctxs))

class Diff (f ::  (* -> *) -> * -> * ) where
  type D f :: (* -> *) -- family name
           -> *        -- type of the hole
           -> *        -- type of surrounding tree
           -> *

instance Diff Unit where
  type D Unit = Zero'

instance Diff (Id xi) where
  type D (Id xi) = Unit' xi

instance (Diff f, Diff g) => Diff (f :+: g) where
  type D (f :+: g) = D f `Sum'` D g

instance (Diff f, Diff g) => Diff (f :*: g) where
  type D (f :*: g) = Prod' (D f) g `Sum'` Prod' (D g) f

instance Diff f => Diff (f ::: ixtag) where
  type D (f ::: ixtag) = Tag' ixtag (D f)

data ExFirst f l ix = forall ixh . Ix l ixh => ExFirst (D f l ixh ix) ixh

class ZipFuns (f :: (* -> *) -> * -> *) where
  firstf :: f l ix -> Maybe (ExFirst f l ix)
  up     :: Ix l ixh => ixh -> D f l ixh ix -> Maybe (f l ix)
  --nextf  :: Ix l ixh => ixh -> D f ixh ix -> Either (ExFirst f l ix) (f l ix)

instance ZipFuns f => ZipFuns (f ::: ixtag) where
  firstf (Tag x)
   = do
     ExFirst ctx h <- firstf x
     return (ExFirst (Tag' ctx) h) 
  up h (Tag' ctx) = liftM Tag (up h ctx)

instance (ZipFuns f, ZipFuns g) => ZipFuns (f :*: g) where
  firstf (x :*: y)
   = do
     ExFirst ctx h <- firstf x
     return (ExFirst (L' (Prod' ctx y)) h)
     `mplus`
     do
     ExFirst ctx h <- firstf y
     return (ExFirst (R' (Prod' ctx x)) h)
  up h (L' (Prod' ctx y)) = liftM (:*:y) (up h ctx)
  up h (R' (Prod' ctx x)) = liftM (x:*:) (up h ctx)
  

instance ZipFuns Unit where
  firstf (K ()) = Nothing
  up ixh zeroval = undefined

instance ZipFuns (Id xi) where
  firstf (Id x) = Just (ExFirst Unit' x)
  up ixh Unit' = Just (Id ixh)

instance (ZipFuns f, ZipFuns g) => ZipFuns (f :+: g) where
  firstf (L x)
   = do
     ExFirst ctx h <- firstf x
     return (ExFirst (L' ctx) h)
  firstf (R x)
   = do
     ExFirst ctx h <- firstf x
     return (ExFirst (R' ctx) h)
  up h (L' ctx) = liftM L (up h ctx)
  up h (R' ctx) = liftM R (up h ctx)


