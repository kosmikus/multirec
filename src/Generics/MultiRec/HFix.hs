{-# LANGUAGE KindSignatures   #-}
{-# LANGUAGE TypeFamilies     #-}
{-# LANGUAGE FlexibleContexts #-}

module Generics.MultiRec.HFix where

import Generics.MultiRec.Base
import Generics.MultiRec.HFunctor

-- * Fixed point of indexed types

data HFix (h :: (* -> *) -> * -> *) ix = HIn { hout :: h (HFix h) ix }

hfrom :: (pfs ~ PF s, Ix s ix, HFunctor (PF s)) => ix -> HFix (pfs s) ix
hfrom = HIn . hmap (const (hfrom . unI0)) . from

hto :: (pfs ~ PF s, Ix s ix, HFunctor (PF s)) => HFix (pfs s) ix -> ix
hto = to . hmap (const (I0 . hto)) . hout
