\begin{code}
module FullTree where

import Generics.MultiRec.Gen
import BinTreeDatatype
import BinTreeReps
import ListRep

genBinTree :: Int -> [BinTree Char]
genBinTree n = gen n BinTree

genList :: Int -> [[Char]]
genList n = gen n List

{-
genWTree :: Int -> [WTree Int Int]
genWTree = fulltree
-}
\end{code}
