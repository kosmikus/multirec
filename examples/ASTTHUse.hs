{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE KindSignatures        #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE TypeSynonymInstances  #-}
{-# LANGUAGE EmptyDataDecls        #-}
{-# LANGUAGE TemplateHaskell       #-}

module ASTTHUse where

import Generics.MultiRec.Base
import Generics.MultiRec.TH
import AST

-- * Instantiating the library for AST using TH

-- ** Index type

data AST :: * -> * where
  Expr  ::  AST Expr
  Decl  ::  AST Decl
  Var   ::  AST Var

-- ** Constructors

$(deriveConstructors [''Expr, ''Decl, ''Var])

-- ** Functor encoding and 'Ix' instances

$(deriveSystem ''AST [''Expr, ''Decl, ''Var] "PFAST")
type instance PF AST = PFAST

