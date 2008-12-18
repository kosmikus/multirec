\begin{code}
module GMap where

import Generics.MultiRec.GMap
import ListRepF
import BinTreeDatatype
import BinTreeRepsF
import Control.Applicative (Const(..))

mapList :: (a -> b) -> [a] -> [b]
mapList f as = gmap List f as

mapListBTree :: (a -> b) -> [BinTree a] -> [BinTree b]
mapListBTree f ts = gmap List (gmap BinTree f) ts

mapListBTreeList :: (a -> b) -> [BinTree [a]] -> [BinTree [b]]
mapListBTreeList f ts = gmap List (gmap BinTree (gmap List f)) ts
\end{code}
