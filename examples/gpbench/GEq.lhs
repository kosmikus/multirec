\begin{code}
module GEq where

import Generics.MultiRec
import BinTreeDatatype
import BinTreeReps
import CompanyDatatypes
import CompanyReps

equalBTreeInt :: BinTree Int -> BinTree Int -> Bool
equalBTreeInt = eq BinTree

equalCompany :: Company -> Company -> Bool
equalCompany = eq Company
\end{code}
