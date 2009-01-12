{-# LANGUAGE FlexibleContexts      #-}

module SingleExamples where

import Generics.MultiRec.Base
import Generics.MultiRec.FoldK

-- Replace SingleUse with SingleTHUse below if you want
-- to test TH code generation.
import SingleUse
import Single

-- | The type LogicAlg is the algebra for the data type Logic
type LogicAlg a = 
  ( String -> a, 
    a -> a -> a, 
    a -> a -> a, 
    a -> a -> a, 
    a -> a -> a, 
    a -> a, 
    a, 
    a
  )

logicAlgebra :: LogicAlg a -> Algebra LogicF a
logicAlgebra (var, impl, equiv, and, or, not, true, false) _ =
                tag (
                        con (\(K s) -> var s)
                      & con (\(I (K0 l1) :*: I (K0 l2)) -> l1 `impl`  l2)
                      & con (\(I (K0 l1) :*: I (K0 l2)) -> l1 `equiv` l2)
                      & con (\(I (K0 l1) :*: I (K0 l2)) -> l1 `and`   l2)
                      & con (\(I (K0 l1) :*: I (K0 l2)) -> l1 `or`    l2)
                      & con (\(I (K0 l)) -> not l)
                      & con (\_ -> true)
                      & con (\_ -> false)
                     )

-- | evalLogic takes a function that gives a logic values to variables,
-- | and a Logic expression, and evaluates it.
evalLogic :: (String -> Bool) -> Logic -> Bool
evalLogic env = fold (logicAlgebra (env, impl, (==), (&&), (||), not, True, False))
 where
   impl p q = not p || q
