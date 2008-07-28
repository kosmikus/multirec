{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE KindSignatures        #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE TypeSynonymInstances  #-}

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
            |  Seq    Decl  Decl
  deriving Show

type Var   =  String

-- * Instantiating the library for AST 

data AST :: * -> * where
  Expr  ::  AST Expr
  Decl  ::  AST Decl
  Var   ::  AST Var

type instance PF AST  =    
                   K Int                  :>:  Expr  -- |Const|
              :+:  (I Expr :*: I Expr)    :>:  Expr  -- |Add|
              :+:  (I Expr :*: I Expr)    :>:  Expr  -- |Mul|
              :+:  I Var                  :>:  Expr  -- |EVar|
              :+:  (I Decl :*: I Expr)    :>:  Expr  -- |Let|
              :+:  (I Var :*: I Expr)     :>:  Decl  -- |:=|
              :+:  (I Decl :*: I Decl)    :>:  Decl  -- |Seq|
              :+:  K String               :>:  Var   -- |V|

instance Ix AST Expr where

  from_ (Const i)   =  L                     (Tag (K i))
  from_ (Add e f)   =  R (L                  (Tag (I (I0 e) :*: I (I0 f))))
  from_ (Mul e f)   =  R (R (L               (Tag (I (I0 e) :*: I (I0 f)))))
  from_ (EVar x)    =  R (R (R (L            (Tag (I (I0 x))))))
  from_ (Let d e)   =  R (R (R (R (L         (Tag (I (I0 d) :*: I (I0 e)))))))

  to_ (L                     (Tag (K i)))                        =  Const i
  to_ (R (L                  (Tag (I (I0 e) :*: I (I0 f)))))     =  Add e f
  to_ (R (R (L               (Tag (I (I0 e) :*: I (I0 f))))))    =  Mul e f
  to_ (R (R (R (L            (Tag (I (I0 x)))))))                =  EVar x
  to_ (R (R (R (R (L         (Tag (I (I0 d) :*: I (I0 e))))))))  =  Let d e
  
  index  =  Expr

instance Ix AST Decl where

  from_ (x := e)    =  R (R (R (R (R (L      (Tag (I (I0 x) :*: I (I0 e))))))))
  from_ (Seq c d)   =  R (R (R (R (R (R (L   (Tag (I (I0 c) :*: I (I0 d)))))))))

  to_ (R (R (R (R (R (L      (Tag (I (I0 x) :*: I (I0 e))))))))) =  x := e
  to_ (R (R (R (R (R (R (L   (Tag (I (I0 c) :*: I (I0 d))))))))))=  Seq c d

  index  =  Decl

instance Ix AST Var where

  from_ x           =  R (R (R (R (R (R (R(Tag (K x))))))))

  to_ (R (R (R (R (R (R (R(Tag (K x)))))))))           =  x

  index  =  Var

