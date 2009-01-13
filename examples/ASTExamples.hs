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
import qualified Generics.MultiRec.Fold as F
import Generics.MultiRec.Fold (con, tag)
import Generics.MultiRec.FoldAlg as FA
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

infixr 5 &.

(&.) = (F.&)

evalAlgebra1 :: F.Algebra AST Value
evalAlgebra1 _ =  
 
      tag  (   con (\ (K x)                   -> EV (const x))
           &.  con (\ (I (EV x) :*: I (EV y)) -> EV (\ env -> x env  +  y env))
           &.  con (\ (I (EV x) :*: I (EV y)) -> EV (\ env -> x env  *  y env))
           &.  con (\ (I (VV x))              -> EV (fromJust . lookup x))
           &.  con (\ (I (DV e) :*: I (EV x)) -> EV (\ env -> x (e env)))
           )
  &.  tag  (   con (\ (I (VV x) :*: I (EV v)) -> DV (\ env -> (x, v env) : env ))
           &.  con (\ (I (DV f) :*: I (DV g)) -> DV (g . f))
           &.  con (\ U                       -> DV id)
           )
  &.  tag          (\ (K x)                   -> VV x)

-- | More convenient algebra for evaluating an expression

evalAlgebra2 :: FA.Algebra AST Value
evalAlgebra2 _ =

     (  (\ x             -> EV (const x))
     &  (\ (EV x) (EV y) -> EV (\ env -> x env  +  y env))
     &  (\ (EV x) (EV y) -> EV (\ env -> x env  *  y env))
     &  (\ (VV x)        -> EV (fromJust . lookup x))
     &  (\ (DV e) (EV x) -> EV (\ env -> x (e env)))
     )
  &  (  (\ (VV x) (EV v) -> DV (\ env -> (x, v env) : env ))
     &  (\ (DV f) (DV g) -> DV (g . f))
     &  (                   DV id)
     )
  &     (\ x             -> VV x)

-- | Evaluator

eval1 :: Expr -> Env -> Int
eval1 x = let (EV f) = F.fold evalAlgebra1 x in f

-- | Evaluator

eval2 :: Expr -> Env -> Int
eval2 x = let (EV f) = FA.fold evalAlgebra2 x in f

-- | Test for 'eval1'

testEval1 :: Int
testEval1 = eval1 example [("y", -12)] 

-- | Test for 'eval2'

testEval2 :: Int
testEval2 = eval2 example [("y", -12)] 

-- | Equality instance for 'Expr'

instance Eq Expr where
  (==) = eq Expr

-- | Test for equality

testEq :: (Bool, Bool)
testEq = (example == example, example == testRename)

-- | Test for generic show

testShow :: IO ()
testShow = putStrLn $ GS.show Expr example
