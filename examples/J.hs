{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE KindSignatures        #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE TypeSynonymInstances  #-}
{-# LANGUAGE EmptyDataDecls        #-}
{-# LANGUAGE TemplateHaskell       #-}
{-# LANGUAGE FlexibleInstances     #-}

module J where

import Generics.MultiRec.Base
import Generics.MultiRec.TH

-- Issue #4 test case

data J a = JJ (a, J a)

data AST :: * -> * -> * where
  J :: AST a (J a)

$(deriveAll ''AST)
