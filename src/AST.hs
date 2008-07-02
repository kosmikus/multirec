{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE KindSignatures        #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeOperators         #-}

module AST where

import Base
import Compos

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
  from (x := e)               = L (Tag (K x :*: Id e))
  to (L (Tag (K x :*: Id e))) = x := e
  ix                          = Decl
 
instance Ix AST Exp where
  from (Var x    ) = R(L     (Tag (K x            )))
  from (Abs x  e ) = R(R(L   (Tag (K x   :*: Id e ))))
  from (App e1 e2) = R(R(R(L (Tag (Id e1 :*: Id e2)))))
  from (Let d  e ) = R(R(R(R (Tag (Id d  :*: Id e )))))

  to (R(L     (Tag (K x              )))) = Var x
  to (R(R(L   (Tag (K x   :*: Id e)  )))) = Abs x  e
  to (R(R(R(L (Tag (Id e1 :*: Id e2)))))) = App e1 e2 
  to (R(R(R(R (Tag (Id d  :*: Id e) ))))) = Let d  e

  ix = Exp

-------------------------------------------------------------------------------
-- application: prepend an underscore to every variable in an abstract-syntax
-- tree
-------------------------------------------------------------------------------
rename_ :: Ix AST ix => AST ix -> ix -> ix 
rename_ Decl (x := e)  = ("_" ++ x) := (rename_ Exp e)
rename_ Exp  (Var x)   = Var ("_" ++ x)
rename_ Exp  (Abs x e) = Abs ("_" ++ x) (rename_ Exp e)
rename_ _    e         = composOp rename_ e

rename :: Exp -> Exp
rename = rename_ Exp

-------------------------------------------------------------------------------
-- test
-------------------------------------------------------------------------------

test :: Exp
test =  rename e
  where
    e = Let ("id" := Abs "x" (Var "x")) (App (Var "id") (Var "y"))
