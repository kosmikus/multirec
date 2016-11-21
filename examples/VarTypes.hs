{-# LANGUAGE EmptyDataDecls        #-}
{-# LANGUAGE TemplateHaskell       #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE KindSignatures        #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module VarTypes where

import Generics.MultiRec.TH

data Type1 a b = CA a | CB b
data Type2 c   = CC c | CD
data Type3     = CE

data TypesF :: * -> * -> * -> * -> * where
  Type1 :: TypesF a b c (Type1 a b)
  Type2 :: TypesF a b c (Type2 c)
  Type3 :: TypesF a b c  Type3

$(deriveAll ''TypesF)

