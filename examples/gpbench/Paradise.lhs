\begin{code}
{-# LANGUAGE FlexibleContexts #-}
module Paradise where

import Generics.MultiRec
import CompanyDatatypes
import CompanyReps

increase :: Float -> Company -> Company
increase f = increase' Company
  where
    increase' :: Ix CompanyU a => CompanyU a -> a -> a
    increase' Salary (S s) = S $ (1 + f) * s
    increase' _ x = compos increase' x
\end{code}
