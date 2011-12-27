{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE KindSignatures        #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE TypeSynonymInstances  #-}
{-# LANGUAGE EmptyDataDecls        #-}

module AST where

import Generics.MultiRec.Base

-- * The AST type from the paper

infix 1 :=

data Expr a =  Const  Int
            |  Add    (Expr a)  (Expr a)
            |  Mul    (Expr a)  (Expr a)
            |  EVar   (Var a)
            |  Let    (Decl a)  (Expr a)
  deriving Show

data Decl a =  Var a := Expr a
            |  Seq    [Decl a]
            |  None
  deriving Show

type Var a  =  a

