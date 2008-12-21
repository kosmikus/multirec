{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE EmptyDataDecls #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE TypeFamilies #-}

import THGen

import Generics.MultiRec.Base
import Generics.MultiRec.Constructor
import Generics.MultiRec.Show as GS

data Expr   =  Const  Int
            |  Add    Expr  Expr
            |  Mul    Expr  Expr
            |  EVar   Var
            |  Let    Decl  Expr
  deriving Show

data Decl   =  Assign Var Expr
            |  Seq    Decl  Decl
  deriving Show

type Var    =  String

data AST :: * -> * where
  Expr  ::  AST Expr
  Decl  ::  AST Decl
  Var   ::  AST Var

$(getConstrs ''Expr)
$(getConstrs ''Decl)

$(getPF "PFAST" [''Expr, ''Decl, ''Var])
type instance PF AST = PFAST
$(ixInstances ''AST [''Expr, ''Decl, ''Var])

exprShow = GS.show Expr
