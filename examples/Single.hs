module Single where

import Generics.MultiRec.Base


-- * A single datatype

data Logic = Var String
           | Logic :->:  Logic            -- implication
           | Logic :<->: Logic            -- equivalence
           | Logic :&&:  Logic            -- and (conjunction)
           | Logic :||:  Logic            -- or (disjunction)
           | Not Logic                    -- not
           | T                            -- true
           | F                            -- false
 deriving (Show, Eq, Ord)
