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

-- ** 'Ix' instances

instance Ix LogicF Logic where

  from_ (Var s)       = Tag (L                   (C (K s)))
  from_ (l1 :->: l2)  = Tag (R (L                (C (I (I0 l1) :*: I (I0 l2)))))
  from_ (l1 :<->: l2) = Tag (R (R (L             (C (I (I0 l1) :*: I (I0 l2))))))
  from_ (l1 :&&: l2)  = Tag (R (R (R (L          (C (I (I0 l1) :*: I (I0 l2)))))))
  from_ (l1 :||: l2)  = Tag (R (R (R (R (L       (C (I (I0 l1) :*: I (I0 l2))))))))
  from_ (Not l)       = Tag (R (R (R (R (R (L    (C (I (I0 l)))))))))
  from_ T             = Tag (R (R (R (R (R (R (L (C U))))))))
  from_ F             = Tag (R (R (R (R (R (R (R (C U))))))))

  to_ (Tag (L                   (C (K s))))                         = Var s
  to_ (Tag (R (L                (C (I (I0 l1) :*: I (I0 l2))))))    = l1 :->: l2
  to_ (Tag (R (R (L             (C (I (I0 l1) :*: I (I0 l2)))))))   = l1 :<->: l2
  to_ (Tag (R (R (R (L          (C (I (I0 l1) :*: I (I0 l2))))))))  = l1 :&&: l2
  to_ (Tag (R (R (R (R (L       (C (I (I0 l1) :*: I (I0 l2))))))))) = l1 :||: l2
  to_ (Tag (R (R (R (R (R (L    (C (I (I0 l))))))))))               = Not l
  to_ (Tag (R (R (R (R (R (R (L (C U)))))))))                       = T
  to_ (Tag (R (R (R (R (R (R (R (C U)))))))))                       = F

  index  =  Logic
