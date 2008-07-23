{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes       #-}

module Generics.MultiRec.Compos where

import Generics.MultiRec.Base
import Generics.MultiRec.HFunctor

compos :: (Ix s ix, HFunctor (PF s)) =>
          (forall ix. Ix s ix => s ix -> ix -> ix) -> ix -> ix
compos f = to . hmap (\ ix -> I0 . f ix . unI0) . from

