{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Transform where

import Base
import Compos
import HMap

-- this function is painful to define for various reasons
-- * composOp needs an index consuming argument so we would need
--   to write "const (transform f)", but this makes a function of
--   type |forall ix. Ix l ix => l1 ix -> ix -> ix
-- * So we are forced to associate the two with a type signature.

transform :: forall l ix . (Ix l ix, HMap (PF l)) =>
             (forall ix. Ix l ix => l ix -> ix -> ix) -> ix -> ix
transform f = f ix . composOp helper
  where
    helper :: forall ix. Ix l ix => l ix -> ix -> ix
    helper w = transform f