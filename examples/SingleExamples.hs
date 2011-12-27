{-# LANGUAGE FlexibleContexts      #-}

module SingleExamples where

import Generics.MultiRec.Base
import Generics.MultiRec.FoldAlgK

-- Replace SingleUse with SingleTHUse below if you want
-- to test TH code generation.
import qualified SingleUse
import SingleTHUse
import Single

-- | evalLogic takes a function that gives a logic values to variables,
-- | and a Logic expression, and evaluates it.
evalLogic :: (String -> Bool) -> Logic -> Bool
evalLogic env = fold algebra Logic
 where
   algebra :: Algebra LogicF Bool
   algebra _ = env & impl & (==) & (&&) & (||) & not & True & False

   impl p q = not p || q
