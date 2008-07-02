{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes       #-}

module Compos where

import Base
import HMap

composOp :: (Ix l ix, HMap (PF l)) =>
            (forall ix. Ix l ix => l ix -> ix -> ix) -> ix -> ix
composOp f = to . hmap f . from