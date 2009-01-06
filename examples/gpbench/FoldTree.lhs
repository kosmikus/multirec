\begin{code}
{-# LANGUAGE FlexibleContexts #-}
module FoldTree where

import Generics.MultiRec
import CompanyDatatypes
import CompanyReps
import TreeDatatype
import TreeReps
import Control.Applicative (Const(..))

selectSalary :: Company -> [Salary]
selectSalary c =
    let collectAlgebra :: Algebra CompanyU (Const [Salary])
        collectAlgebra _ = tag (con (\(I (Const ds)) -> Const ds))
                         & tag (\(K ()) -> Const [])
                         & tag (\(I (Const ds) :*: I (Const dss)) -> Const (ds ++ dss))
                         & tag (con (\(_ :*: I (Const es) :*: I (Const uss)) ->  Const (es ++ uss)))
                         & tag (\(K ()) -> Const [])
                         & tag (\(I (Const us) :*: I (Const uss)) -> Const (us ++ uss))
                         & tag (con (\(I (Const es)) -> Const es))
                         & tag (con (\(I (Const ds)) -> Const ds))
                         & tag (con (\(I (Const ps) :*: I (Const ss)) -> Const (ps ++ ss)))
                         & tag (con (\_ -> Const []))
                         & tag (con (\(K s) -> Const [S s]))
        (Const ss) = fold collectAlgebra c
    in ss

selectIntWTree :: WTree Int Int -> [Int]
selectIntWTree t =
    let collectAlgebra :: Algebra (WTreeU Int Int) (Const [Int])
        collectAlgebra _ = tag (\(K i) -> Const [i])
                         & tag (\(I (Const l) :*: I (Const r)) -> Const (l ++ r))
                         & tag (\(I (Const t) :*: K w) -> Const (t ++ [w]))
        (Const is) = fold collectAlgebra t
    in is
\end{code}
