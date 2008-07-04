{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE KindSignatures        #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeOperators         #-}

module AST where

import Base
import ShowFam

-------------------------------------------------------------------------------
-- a system of mutually recursive types for representing abstract syntax
-------------------------------------------------------------------------------

infix 1 :=

type Var  = String
data Decl = Var := Exp deriving Show
data Exp  = Var Var | Abs Var Exp | App Exp Exp | Let Decl Exp deriving Show

-------------------------------------------------------------------------------
-- grouping the mutual recursive types in a family
-------------------------------------------------------------------------------

data AST :: * -> * where
  Decl :: AST Decl
  Exp  :: AST Exp

instance Fam AST where
  type PF AST = K Var   :*: Id Exp  ::: Decl  :+:    -- (:=)
                K Var               ::: Exp   :+:    -- Var
                K Var   :*: Id Exp  ::: Exp   :+:    -- Abs
                Id Exp  :*: Id Exp  ::: Exp   :+:    -- App
                Id Decl :*: Id Exp  ::: Exp          -- Let

instance Ix AST Decl where
  ix                          = Decl
  from (x := e)               = L (Tag (K x :*: Id e))
  to (L (Tag (K x :*: Id e))) = x := e
 
instance Ix AST Exp where
  ix                                      = Exp

  from (Var x    )                        = R(L     (Tag (K x            )))
  from (Abs x  e )                        = R(R(L   (Tag (K x   :*: Id e ))))
  from (App e1 e2)                        = R(R(R(L (Tag (Id e1 :*: Id e2)))))
  from (Let d  e )                        = R(R(R(R (Tag (Id d  :*: Id e )))))

  to (R(L     (Tag (K x              )))) = Var x
  to (R(R(L   (Tag (K x   :*: Id e)  )))) = Abs x  e
  to (R(R(R(L (Tag (Id e1 :*: Id e2)))))) = App e1 e2 
  to (R(R(R(R (Tag (Id d  :*: Id e) ))))) = Let d  e

-------------------------------------------------------------------------------
-- pretty printing
-------------------------------------------------------------------------------

instance ShowFam AST where
  showFam Decl = show
  showFam Exp  = show