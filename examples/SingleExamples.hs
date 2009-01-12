{-# LANGUAGE FlexibleContexts      #-}

module SingleExamples where

import Generics.MultiRec.Base
import Generics.MultiRec.BetterFoldK

-- Replace SingleUse with SingleTHUse below if you want
-- to test TH code generation.
import SingleUse
import Single

-- | evalLogic takes a function that gives a logic values to variables,
-- | and a Logic expression, and evaluates it.
evalLogic :: (String -> Bool) -> Logic -> Bool
evalLogic env = fold' Logic (const $ env & impl & (==) & (&&) & (||) & not & True & False)
 where
   impl p q = not p || q
