{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE KindSignatures        #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE FunctionalDependencies#-}

module Base where

-------------------------------------------------------------------------------
-- structure types
-------------------------------------------------------------------------------

infixr 5 :+:
infix  6 :::
infixr 7 :*:

data Id :: * -> (* -> *) -> * -> * where
  Id :: Ix l xi => xi -> Id xi l ix

unId :: Id xi l ix -> xi
unId (Id x) = x

data K a       (l :: * -> *) ix = K {unK :: a}
data (f :+: g) (l :: * -> *) ix = L (f l ix) | R (g l ix)
data (f :*: g) (l :: * -> *) ix = f l ix :*: g l ix

data (:::) :: ((* -> *) -> * -> *) -> * -> (* -> *) -> * -> * where
  Tag {unTag :: f l ix} :: (f ::: ix) l ix

-------------------------------------------------------------------------------
-- indexed families, generically
-------------------------------------------------------------------------------

class Fam l where
  type PF l :: (* -> *) -> * -> *

type Str l ix = (PF l) l ix

class Fam l => Ix l ix where
  from :: ix -> Str l ix
  to   :: Str l ix -> ix
  ix   :: l ix
