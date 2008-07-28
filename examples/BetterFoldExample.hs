{-# LANGUAGE TypeFamilies     #-}
{-# LANGUAGE FlexibleContexts #-}

module BetterFoldExample where

import AST
import Data.Maybe
import Generics.MultiRec.BetterFold

data family Value aT :: *
data instance Value Expr  =  EV (Env -> Int)
data instance Value Decl  =  DV (Env -> Env)
data instance Value Var   =  VV Var

type Env = [(Var, Int)]

evalAlg :: Algebra AST Value
evalAlg _ = (\ x             -> EV (const x)) 
          & (\ (EV x) (EV y) -> EV (\ env -> x env + y env))
          & (\ (EV x) (EV y) -> EV (\ env -> x env * y env))
          & (\ (VV x)        -> EV (fromJust . lookup x))
          & (\ (DV e) (EV x) -> EV (\ env -> x (e env)))
          & (\ (VV x) (EV v) -> DV (\ env -> (x, v env) : env))
          & (\ (DV f) (DV g) -> DV (g . f))
          & (\ x             -> VV x)

example = Let ("x" := Mul (Const 6) (Const 9))
              (Add (EVar "x") (EVar "y"))

eval :: Expr -> Env -> Int
eval x = let (EV f) = fold evalAlg x in f

testEval :: Int
testEval = eval example [("y", -12)] 
