module MultiParam.RTree where

-- Tree with list, to test composition

data RTree a = RTree a [RTree a] deriving Show
