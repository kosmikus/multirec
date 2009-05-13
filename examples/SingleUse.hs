{-# LANGUAGE EmptyDataDecls        #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE KindSignatures        #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeOperators         #-}

module SingleUse where

import Generics.MultiRec.Base
import Single

-- * Instantiating the library for Logic 

-- ** Index type

data LogicF :: * -> * where
  Logic ::  LogicF Logic

-- ** Constructors

data Var
instance Constructor Var   where conName _   = "Var"

data Impl
instance Constructor Impl  where
  conName _   = ":->:"
  conFixity _ = Infix RightAssociative 2

data Equiv
instance Constructor Equiv where
  conName _ = ":<->:"
  conFixity _ = Infix RightAssociative 1

data And
instance Constructor And   where
  conName _ = ":&&:"
  conFixity _ = Infix RightAssociative 4

data Or
instance Constructor Or    where
  conName _ = ":||:"
  conFixity _ = Infix RightAssociative 3

data Not
instance Constructor Not   where conName _ = "Not"
data T
instance Constructor T     where conName _ = "T"
data F
instance Constructor F     where conName _ = "F"

-- ** Functor encoding

type instance PF LogicF  =    
      (     C Var   (K String)
       :+:  C Impl  (I Logic :*: I Logic)
       :+:  C Equiv (I Logic :*: I Logic)
       :+:  C And   (I Logic :*: I Logic)
       :+:  C Or    (I Logic :*: I Logic)
       :+:  C Not   (I Logic)
       :+:  C T     U
       :+:  C F     U
      ) :>: Logic

-- ** 'El' instance

instance El LogicF Logic where proof = Logic

-- ** 'Fam' instance

instance Fam LogicF where

  from Logic (Var s)       = Tag (L                   (C (K s)))
  from Logic (l1 :->: l2)  = Tag (R (L                (C (I (I0 l1) :*: I (I0 l2)))))
  from Logic (l1 :<->: l2) = Tag (R (R (L             (C (I (I0 l1) :*: I (I0 l2))))))
  from Logic (l1 :&&: l2)  = Tag (R (R (R (L          (C (I (I0 l1) :*: I (I0 l2)))))))
  from Logic (l1 :||: l2)  = Tag (R (R (R (R (L       (C (I (I0 l1) :*: I (I0 l2))))))))
  from Logic (Not l)       = Tag (R (R (R (R (R (L    (C (I (I0 l)))))))))
  from Logic T             = Tag (R (R (R (R (R (R (L (C U))))))))
  from Logic F             = Tag (R (R (R (R (R (R (R (C U))))))))

  to Logic (Tag (L                   (C (K s))))                         = Var s
  to Logic (Tag (R (L                (C (I (I0 l1) :*: I (I0 l2))))))    = l1 :->: l2
  to Logic (Tag (R (R (L             (C (I (I0 l1) :*: I (I0 l2)))))))   = l1 :<->: l2
  to Logic (Tag (R (R (R (L          (C (I (I0 l1) :*: I (I0 l2))))))))  = l1 :&&: l2
  to Logic (Tag (R (R (R (R (L       (C (I (I0 l1) :*: I (I0 l2))))))))) = l1 :||: l2
  to Logic (Tag (R (R (R (R (R (L    (C (I (I0 l))))))))))               = Not l
  to Logic (Tag (R (R (R (R (R (R (L (C U)))))))))                       = T
  to Logic (Tag (R (R (R (R (R (R (R (C U)))))))))                       = F
