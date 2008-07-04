{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE KindSignatures        #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeOperators         #-}

module ZigZag where

import Base
import ShowFam

-------------------------------------------------------------------------------
-- going back and forth until we're zapped
-------------------------------------------------------------------------------

data Zig = Zig Zag       deriving Show
data Zag = Zag Zig | Zap deriving Show

-------------------------------------------------------------------------------
-- grouping the mutual recursive types in a family
-------------------------------------------------------------------------------

data ZigZag :: * -> * where
  ZZig :: ZigZag Zig
  ZZag :: ZigZag Zag

instance Fam ZigZag where
  type PF ZigZag = Id Zag  ::: Zig  :+:    -- Zig
                   Id Zig  ::: Zag  :+:    -- Zag
                   K ()    ::: Zag         -- Zap

instance Ix ZigZag Zig where
  ix                  = ZZig
  from (Zig z)        = L (Tag (Id z))
  to (L (Tag (Id z))) = Zig z

instance Ix ZigZag Zag where
  ix                      = ZZag

  from (Zag z)            = R (L (Tag (Id z)))
  from Zap                = R (R (Tag (K ())))

  to (R (L (Tag (Id z)))) = Zag z
  to (R (R (Tag (K ())))) = Zap

-------------------------------------------------------------------------------
-- pretty printing
-------------------------------------------------------------------------------

instance ShowFam ZigZag where
  showFam ZZig = show
  showFam ZZag = show