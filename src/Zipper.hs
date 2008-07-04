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
import Data.Maybe

import Base

-- -----------------------------------------------------------------
-- Representation types for contexts
-- -----------------------------------------------------------------
-- ixh : type of hole
-- ix  : type of tree
data CProd df f (l :: * -> *) ixh ix = CProd (df l ixh ix) (f l ix)

data CSum df dg (l :: * -> *) ixh ix = CL (df l ixh ix) | CR (dg l ixh ix)

data CZero (l :: * -> *) ixh ix

refuteCZero :: CZero l ixh ix -> a
refuteCZero ctxzero = ctxzero `seq` undefined

data CTag ixtag df (l :: * -> *) ixh ix where
  CTag :: df l ixh ix -> CTag ix df l ixh ix

data CHole xi (l :: * -> *) ixh ix where
  CHole :: CHole ixh l ixh ix

type Unit = K ()

-- -----------------------------------------------------------------
-- Zipper datatype and high-level functions
-- -----------------------------------------------------------------
data Zipper l ix where
  Zipper :: Ix l ixh => ixh -> (CList l ixh ix) -> Zipper l ix

data CList l ixh ix where
  CNil  :: CList l ix ix
  CCons :: Ix l ix => D (PF l) l ixh ix -> CList l ix ix' -> CList l ixh ix' 

-- renamed toZipper to ...
enter :: Ix l ix => ix -> Zipper l ix
enter x = Zipper x CNil

-- leave merges everything together again, because we otherwise don't
-- know what type to return ...
leave :: (ZipFuns (PF l), Ix l ix) => Zipper l ix -> ix
leave (Zipper x CNil) = x
leave x               = leave (up' x)

update :: (forall ix. Ix l ix => ix -> ix) -> Zipper l ix -> Zipper l ix
update f (Zipper x ctx) = Zipper (f x) ctx

applyZipper :: (forall ix . l ix -> ix -> a) -> Zipper l ix -> a
applyZipper f (Zipper x _) = f ix x

down :: forall l ix . ZipFuns (PF l) => Zipper l ix -> Maybe (Zipper l ix)
down (Zipper (x::ix') ctxs)
  = do
    CtxOf ctx x' <- firstf (from' x) :: Maybe (CtxOf (PF l) l ix')
    return (Zipper x' (CCons ctx ctxs))

-- variant of down that cannot fail
down' :: forall l ix . ZipFuns (PF l) => Zipper l ix -> Zipper l ix
down' z = maybe z id (down z)

up :: forall l ix . ZipFuns (PF l) => Zipper l ix -> Maybe (Zipper l ix)
up (Zipper _ CNil) = Nothing
up (Zipper (x::ixh) (CCons ctx ctxs)) = Just (Zipper (to' (upf' x ctx)) ctxs)
 
-- variant again
up' :: forall l ix . ZipFuns (PF l) => Zipper l ix -> Zipper l ix
up' z = maybe z id (up z)

-- ---------------------------
-- Wrappers that use equality constraints
--  -----------------------------
from' :: forall l pf ix . (Ix l ix,PF l ~ pf) => ix -> pf l ix
from' = from

--firstf' ::  forall l ix ixh df f . ZipFuns f) => f l ix -> Maybe (CtxOf f l ix)

upf' :: forall l ix ixh df f . (Ix l ixh,df ~ D f,ZipFuns f) => ixh -> df l ixh ix -> f l ix
upf' = upf

to'  :: forall l pf ix . (Ix l ix,PF l ~ pf) => pf l ix -> ix
to' = to
 
-- -----------------------------------------------------------------
-- D operator
-- -----------------------------------------------------------------
type family D f :: (* -> *) -- family name
                -> *        -- type of the hole
                -> *        -- type of surrounding tree
                -> *
type instance D (K a)         = CZero
type instance D (Id xi)       = CHole xi
type instance D (f :+: g)     = D f `CSum` D g
type instance D (f :*: g)     = CProd (D f) g `CSum` CProd (D g) f
type instance D (f ::: ixtag) = CTag ixtag (D f)

data CtxOf f l ix = forall ixh . Ix l ixh => CtxOf (D f l ixh ix) ixh

mapCtxOf :: (forall ixh . D f l ixh ix -> D f' l ixh ix)
         -> CtxOf f l ix -> CtxOf f' l ix
mapCtxOf f (CtxOf ctx x) = CtxOf (f ctx) x

-- variant for mapping over a Maybe
mapMbCtxOf :: (forall ixh . D f l ixh ix -> D f' l ixh ix)
           -> Maybe (CtxOf f l ix) -> Maybe (CtxOf f' l ix)
mapMbCtxOf = liftM . mapCtxOf

-- -----------------------------------------------------------------
-- Zipper generic functions
-- -----------------------------------------------------------------
class ZipFuns (f :: (* -> *) -> * -> *) where
  firstf :: f l ix -> Maybe (CtxOf f l ix)
  upf    :: Ix l ixh => ixh -> D f l ixh ix -> f l ix
  --nextf  :: Ix l ixh => ixh -> D f ixh ix -> Either (CtxOf f l ix) (f l ix)

instance ZipFuns f => ZipFuns (f ::: ixtag) where
  firstf (Tag x)   = mapMbCtxOf CTag (firstf x)
  upf h (CTag ctx) = Tag (upf h ctx)

instance (ZipFuns f, ZipFuns g) => ZipFuns (f :*: g) where
  firstf (x :*: y) = mapMbCtxOf (CL . (`CProd` y)) (firstf x) `mplus`
                     mapMbCtxOf (CR . (`CProd` x)) (firstf y)
  upf h (CL (CProd ctx y)) = upf h ctx :*: y
  upf h (CR (CProd ctx x)) = x         :*: upf h ctx

instance ZipFuns (K a) where
  firstf (K _)    = Nothing
  upf ixh ctxzero = refuteCZero ctxzero

instance ZipFuns (Id xi) where
  firstf (Id x) = Just (CtxOf CHole x)
  upf ixh CHole = Id ixh

instance (ZipFuns f, ZipFuns g) => ZipFuns (f :+: g) where
  firstf (L x) = mapMbCtxOf CL (firstf x)
  firstf (R x) = mapMbCtxOf CR (firstf x)
  upf h (CL ctx) = L (upf h ctx)
  upf h (CR ctx) = R (upf h ctx)


