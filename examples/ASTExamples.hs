{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE LiberalTypeSynonyms  #-}
{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE GADTs                #-}

module ASTExamples where

import Data.Maybe (fromJust)
import Control.Arrow ((>>>))
import Control.Monad ((>=>))

-- Replace ASTUse with ASTTHUse below if you want
-- to test TH code generation.
import qualified ASTUse
import ASTTHUse
import AST

import Generics.MultiRec.Base
import Generics.MultiRec.Compos
import qualified Generics.MultiRec.Fold as F
import Generics.MultiRec.Fold (con, tag)
import Generics.MultiRec.FoldAlg as FA
import Generics.MultiRec.Eq
import Generics.MultiRec.Show as GS
import Generics.MultiRec.Read as GR

-- | Example expression

example = Let (Seq ["x" := Mul (Const 6) (Const 9), "z" := Const 1])
              (Mul (EVar "z") (Add (EVar "x") (EVar "y")))

-- | Renaming variables using 'compos'

renameVar :: Expr String -> Expr String
renameVar = renameVar' Expr
  where
    renameVar' :: AST String a -> a -> a
    renameVar' Var x = x ++ "_"
    renameVar' p   x = compos renameVar' p x

-- | Test for 'renameVar'

testRename :: Expr String
testRename = renameVar example

-- | Result of evaluating an expression

data family Value aT :: *
data instance Value (Expr String)  =  EV  (Env -> Int)
data instance Value (Decl String)  =  DV  (Env -> Env)
data instance Value (Var String)   =  VV  (Var String)

type Env = [(Var String, Int)]

-- | Algebra for evaluating an expression

infixr 5 &.

(&.) = (F.&)

evalAlgebra1 :: F.Algebra (AST String) Value
evalAlgebra1 _ =

      tag  (   con (\ (K x)                   -> EV (const x))
           &.  con (\ (I (EV x) :*: I (EV y)) -> EV (\ env -> x env  +  y env))
           &.  con (\ (I (EV x) :*: I (EV y)) -> EV (\ env -> x env  *  y env))
           &.  con (\ (I (VV x))              -> EV (fromJust . lookup x))
           &.  con (\ (I (DV e) :*: I (EV x)) -> EV (\ env -> x (e env)))
           )
  &.  tag  (   con (\ (I (VV x) :*: I (EV v)) -> DV (\ env -> (x, v env) : env ))
           &.  con (\ (D fs)                  -> DV (foldl (\ f (I (DV g)) -> f . g) id fs))
           &.  con (\ U                       -> DV id)
           )
  &.  tag          (\ (K x)                   -> VV x)

-- | More convenient algebra for evaluating an expression

evalAlgebra2 :: FA.Algebra (AST String) Value
evalAlgebra2 _ =

     (  (\ x             -> EV (const x))
     &  (\ (EV x) (EV y) -> EV (\ env -> x env  +  y env))
     &  (\ (EV x) (EV y) -> EV (\ env -> x env  *  y env))
     &  (\ (VV x)        -> EV (fromJust . lookup x))
     &  (\ (DV e) (EV x) -> EV (\ env -> x (e env)))
     )
  &  (  (\ (VV x) (EV v) -> DV (\ env -> (x, v env) : env ))
     &  (\ fs            -> DV (foldl (\ f (DV g) -> f . g) id fs))
     &  (                   DV id)
     )
  &     (\ x             -> VV x)

-- | Evaluator

eval1 :: Expr String -> Env -> Int
eval1 x = let (EV f) = F.fold evalAlgebra1 Expr x in f

-- | Evaluator

eval2 :: Expr String -> Env -> Int
eval2 x = let (EV f) = FA.fold evalAlgebra2 Expr x in f

-- | Test for 'eval1'

testEval1 :: Int
testEval1 = eval1 example [("y", -12)]

-- | Test for 'eval2'

testEval2 :: Int
testEval2 = eval2 example [("y", -12)]

-- | Equality instance for 'Expr'

instance Eq a => Eq (Expr a) where
  (==) = eq Expr

-- | Test for equality

testEq :: (Bool, Bool)
testEq = (example == example, example == testRename)

-- | Test for generic show

testShow :: IO ()
testShow = putStrLn $ GS.show Expr example

-- | Test for generic show, read and equality

testReadShowEq :: Bool
testReadShowEq = GR.read Expr (GS.show Expr example) == example
