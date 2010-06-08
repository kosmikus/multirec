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

data Expr   =  Const  Int
            |  Add    Expr  Expr
            |  Mul    Expr  Expr
            |  EVar   Var
            |  Let    Decl  Expr
  deriving Show

data Decl   =  Var := Expr
            |  Seq    [Decl]
            |  None
  deriving Show

type Var   =  String

