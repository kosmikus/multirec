{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs            #-}

module ComposTest where

import AST
import Base
import Compos

-------------------------------------------------------------------------------
-- prepend an underscore to every variable in an abstract-syntax tree
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