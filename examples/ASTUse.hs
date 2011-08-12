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
       :+:  C Seq     ([] :.: I Decl)
       :+:  C None    U
      ) :>: Decl
  :+: (               (K String)
      ) :>: Var

-- ** 'El' instances

instance El AST Expr where proof = Expr
instance El AST Decl where proof = Decl
instance El AST Var  where proof = Var

-- ** 'Fam' instance

instance Fam AST where

  from Expr (Const i)  =  L (Tag (L          (C (K i))))
  from Expr (Add e f)  =  L (Tag (R (L       (C (I (I0 e) :*: I (I0 f))))))
  from Expr (Mul e f)  =  L (Tag (R (R (L    (C (I (I0 e) :*: I (I0 f)))))))
  from Expr (EVar x)   =  L (Tag (R (R (R (L (C (I (I0 x))))))))
  from Expr (Let d e)  =  L (Tag (R (R (R (R (C (I (I0 d) :*: I (I0 e))))))))

  from Decl (x := e)   =  R (L (Tag (L    (C (I (I0 x) :*: I (I0 e))))))
  from Decl (Seq ds)   =  R (L (Tag (R (L (C (D (map (I . I0) ds)))))))
  from Decl (None)     =  R (L (Tag (R (R (C U)))))

  from Var  x          =  R (R (Tag (K x)))

  to Expr (L (Tag (L          (C (K i)))))                       =  Const i
  to Expr (L (Tag (R (L       (C (I (I0 e) :*: I (I0 f)))))))    =  Add e f
  to Expr (L (Tag (R (R (L    (C (I (I0 e) :*: I (I0 f))))))))   =  Mul e f
  to Expr (L (Tag (R (R (R (L (C (I (I0 x)))))))))               =  EVar x
  to Expr (L (Tag (R (R (R (R (C (I (I0 d) :*: I (I0 e)))))))))  =  Let d e

  to Decl (R (L (Tag (L    (C (I (I0 x) :*: I (I0 e)))))))       =  x := e
  to Decl (R (L (Tag (R (L (C (D ds)))))))                       =  Seq (map (unI0 . unI) ds)
  to Decl (R (L (Tag (R (R (C U))))))                            =  None

  to Var  (R (R (Tag (K x))))                                    =  x

-- ** EqS instance

instance EqS AST where
  eqS Expr Expr = Just Refl
  eqS Decl Decl = Just Refl
  eqS Var  Var  = Just Refl
  eqS _    _    = Nothing
