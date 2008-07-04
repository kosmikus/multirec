{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE KindSignatures        #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeOperators         #-}

module Zipper where

import Control.Monad
import Base
import TEq
import Void

-------------------------------------------------------------------------------
-- representation of a tree, with a particular subtree in focus
-------------------------------------------------------------------------------

data Loc :: (* -> *) -> * -> * where
  Loc :: Ix l ix => ix -> Stack l a ix -> Loc l a

data Stack :: (* -> *) -> * -> * -> * where
  Empty :: Stack l a a
  Push  :: Ix l ix => Ctx (PF l) l ix b -> Stack l a ix -> Stack l a b

-------------------------------------------------------------------------------
-- One-hole contexts
-------------------------------------------------------------------------------

data family Ctx f l ix :: * -> *

data instance Ctx (Id xi) l ix b    = CId (b :=: xi)
data instance Ctx (K a) l ix b      = CK Void
data instance Ctx (f :+: g) l ix b  =
                CSum (Either (Ctx f l ix b) (Ctx g l ix b))
data instance Ctx (f :*: g) l ix b  =
                CProd (Either (Ctx f l ix b, g l ix) (f l ix, Ctx g l ix b))
data instance Ctx (f ::: xi) l ix b = CTag (ix :=: xi) (Ctx f l ix b)

-------------------------------------------------------------------------------
-- Zippers functions
-------------------------------------------------------------------------------

class Zipper_ f where
  first :: (forall b. Ix l b => b -> Ctx f l ix b -> a)
        -> f l ix -> Maybe a
  fill  :: Ix l b => Ctx f l ix b -> b -> f l ix

class (Ix l ix, Zipper_ (PF l)) => Zipper l ix

instance Zipper_ (Id xi) where
  first f (Id x)   = return (f x (CId Refl))
  fill (CId prf) x = castId prf Id x

instance Zipper_ (K a) where
  first f (K a)    = Nothing
  fill (CK void) x = refute void

instance (Zipper_ f, Zipper_ g) => Zipper_ (f :+: g) where
  first f (L x)           = first (\z -> f z . CSum . Left) x
  first f (R y)           = first (\z -> f z . CSum . Right) y
  
  fill (CSum (Left  c)) x = L (fill c x)
  fill (CSum (Right c)) y = R (fill c y)

instance (Zipper_ f, Zipper_ g) => Zipper_ (f :*: g) where
  first f (x :*: y) =
    first (\z c -> f z (CProd (Left  (c, y)))) x `mplus`
    first (\z c -> f z (CProd (Right (x, c)))) y

  fill (CProd (Left  (c, y))) x = fill c x :*: y
  fill (CProd (Right (x, c))) y = x :*: fill c y

instance Zipper_ f => Zipper_ (f ::: xi) where
  first f (Tag x)     = first (\z -> f z . CTag Refl) x
  fill (CTag prf c) x = castTag prf Tag (fill c x)

-- helpers
castId  :: (b :=: xi)
        -> (Ix l xi => xi -> Id xi l ix)
        -> (Ix l b  => b  -> Id xi l ix)

castTag :: (ix :=: xi)
        -> (f l ix -> (f ::: ix) l ix)
        -> (f l ix -> (f ::: xi) l ix)

castId  Refl f = f
castTag Refl f = f

-------------------------------------------------------------------------------
-- interface
-------------------------------------------------------------------------------

enter :: Zipper l ix => ix -> Loc l ix
enter x = Loc x Empty

down :: Zipper l ix => Loc l ix -> Maybe (Loc l ix)
down (Loc x s) = first (\z c -> Loc z (Push c s)) (from x)

up :: Zipper l ix => Loc l ix -> Maybe (Loc l ix)
up (Loc x Empty)      = Nothing
up (Loc x (Push c s)) = return (Loc (to (fill c x)) s)