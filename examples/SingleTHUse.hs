{-# LANGUAGE EmptyDataDecls        #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE KindSignatures        #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TemplateHaskell       #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeOperators         #-}

module SingleTHUse where

import Single
import Generics.MultiRec.Base
import Generics.MultiRec.TH


-- * Instantiating multirec for Logic using TH
-- ** Index type
data LogicF :: * -> * where
  Logic :: LogicF Logic

$(deriveAll ''LogicF)
