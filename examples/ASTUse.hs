{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE KindSignatures        #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE TypeSynonymInstances  #-}
{-# LANGUAGE EmptyDataDecls        #-}

module ASTUse where

import Generics.MultiRec.Base
import AST

-- * Instantiating the library for AST 

-- ** Index type

data AST :: * -> * where
  Expr  ::  AST Expr
  Decl  ::  AST Decl
  Var   ::  AST Var

-- ** Constructors

data Const
instance Constructor Const  where conName _ = "Const"
data Add
instance Constructor Add    where conName _ = "Add"
data Mul
instance Constructor Mul    where conName _ = "Mul"
data EVar
instance Constructor EVar   where conName _ = "EVar"
data Let
instance Constructor Let    where conName _ = "Let"
data Assign
instance Constructor Assign where
  conName _ = ":="
  conFixity _ = Infix NotAssociative 1
data Seq
instance Constructor Seq   where conName _ = "Seq"
data None
instance Constructor None  where conName _ = "None"

-- ** Functor encoding

-- Variations of the encoding below are possible. For instance,
-- the 'C' applications can be omitted if no functions that require
-- constructor information are needed. Furthermore, it is possible
-- to tag every constructor rather than every datatype. That makes
-- the overall structure slightly simpler, but makes the nesting
-- of 'L' and 'R' constructors larger in turn.

type instance PF AST  =    
      (     C Const   (K Int)
       :+:  C Add     (I Expr :*: I Expr)
       :+:  C Mul     (I Expr :*: I Expr)
       :+:  C EVar    (I Var)
       :+:  C Let     (I Decl :*: I Expr)
      ) :>: Expr
  :+: (     C Assign  (I Var  :*: I Expr)
       :+:  C Seq     (I Decl :*: I Decl)
       :+:  C None    (K ())
      ) :>: Decl
  :+: (               (K String)
      ) :>: Var

-- ** 'Ix' instances

instance Ix AST Expr where

  from_ (Const i)  =  L (Tag (L          (C (K i))))
  from_ (Add e f)  =  L (Tag (R (L       (C (I (I0 e) :*: I (I0 f))))))
  from_ (Mul e f)  =  L (Tag (R (R (L    (C (I (I0 e) :*: I (I0 f)))))))
  from_ (EVar x)   =  L (Tag (R (R (R (L (C (I (I0 x))))))))
  from_ (Let d e)  =  L (Tag (R (R (R (R (C (I (I0 d) :*: I (I0 e))))))))

  to_ (L (Tag (L          (C (K i)))))                       =  Const i
  to_ (L (Tag (R (L       (C (I (I0 e) :*: I (I0 f)))))))    =  Add e f
  to_ (L (Tag (R (R (L    (C (I (I0 e) :*: I (I0 f))))))))   =  Mul e f
  to_ (L (Tag (R (R (R (L (C (I (I0 x)))))))))               =  EVar x
  to_ (L (Tag (R (R (R (R (C (I (I0 d) :*: I (I0 e)))))))))  =  Let d e

  index  =  Expr

instance Ix AST Decl where

  from_ (x := e)   =  R (L (Tag (L    (C (I (I0 x) :*: I (I0 e))))))
  from_ (Seq c d)  =  R (L (Tag (R (L (C (I (I0 c) :*: I (I0 d)))))))
  from_ (None)     =  R (L (Tag (R (R (C (K ()))))))

  to_ (R (L (Tag (L    (C (I (I0 x) :*: I (I0 e)))))))   =  x := e
  to_ (R (L (Tag (R (L (C (I (I0 c) :*: I (I0 d))))))))  = Seq c d
  to_ (R (L (Tag (R (R (C (K ())))))))                   = None

  index  =  Decl

instance Ix AST Var where

  from_ x  =  R (R (Tag (K x)))

  to_ (R (R (Tag (K x))))  =  x

  index  =  Var

