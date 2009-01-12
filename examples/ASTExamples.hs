{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE TypeFamilies         #-}

module ASTExamples where

import Data.Maybe (fromJust)
import Control.Arrow ((>>>))
import Control.Monad ((>=>))

-- Replace ASTUse with ASTTHUse below if you want
-- to test TH code generation.
import AST
import ASTUse
-- import ASTTHUse

import Generics.MultiRec.Base
import Generics.MultiRec.Compos
import Generics.MultiRec.Fold
import Generics.MultiRec.Eq
import Generics.MultiRec.Show as GS

-- | Example expression

example = Let (Seq ("x" := Mul (Const 6) (Const 9)) None)
              (Add (EVar "x") (EVar "y"))

-- | Renaming variables using 'compos'

renameVar :: Expr -> Expr
renameVar = renameVar' Expr
  where
    renameVar' :: Ix AST a => AST a -> a -> a
    renameVar' Var x = x ++ "_"
    renameVar' _   x = compos renameVar' x

-- | Test for 'renameVar'

testRename :: Expr
testRename = renameVar example

-- | Result of evaluating an expression

data family Value aT :: *
data instance Value Expr  =  EV  (Env -> Int)
data instance Value Decl  =  DV  (Env -> Env)
data instance Value Var   =  VV  Var

type Env = [(Var, Int)]

-- | Algebra for evaluating an expression

evalAlgebra :: Algebra AST Value
evalAlgebra _ =  
 
     tag  (  con (\ (K x)                   -> EV (const x))
          &  con (\ (I (EV x) :*: I (EV y)) -> EV (\ env -> x env  +  y env))
          &  con (\ (I (EV x) :*: I (EV y)) -> EV (\ env -> x env  *  y env))
          &  con (\ (I (VV x))              -> EV (fromJust . lookup x))
          &  con (\ (I (DV e) :*: I (EV x)) -> EV (\ env -> x (e env)))
          )
  &  tag  (  con (\ (I (VV x) :*: I (EV v)) -> DV (\ env -> (x, v env) : env ))
          &  con (\ (I (DV f) :*: I (DV g)) -> DV (g . f))
          &  con (\ (K ())                  -> DV id)
          )
  &  tag         (\ (K x)                   -> VV x)

-- | Evaluator

eval :: Expr -> Env -> Int
eval x = let (EV f) = fold evalAlgebra x in f

-- | Test for 'eval'

testEval :: Int
testEval = eval example [("y", -12)] 

-- | Equality instance for 'Expr'

instance Eq Expr where
  (==) = eq Expr

-- | Test for equality

testEq :: (Bool, Bool)
testEq = (example == example, example == testRename)

-- | Test for generic show

testShow :: IO ()
testShow = putStrLn $ GS.show Expr example
