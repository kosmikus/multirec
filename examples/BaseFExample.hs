{-# LANGUAGE GADTs
           , TypeFamilies
           , TypeOperators
           , KindSignatures
           , MultiParamTypeClasses
           , FlexibleContexts
           #-}
module BaseFExample where

import Data.Char (toUpper)
import Generics.MultiRec.BaseF
import Generics.MultiRec.HFunctorF
import Generics.MultiRec.ComposF

data ListU :: (* -> *) -> * where
    List :: ListU []

type instance PF ListU = K () :>: []
                     :+: E :*: I [] :>: []

instance Ix ListU [] where
    from_ [] = L (Tag (K ()))
    from_ (x : xs) = R (Tag (E x :*: I (I0F xs)))
    to_ (L (Tag (K ()))) = []
    to_ (R (Tag (E x :*: I (I0F xs)))) = x : xs
    index = List

data Company a = C [Dept a] deriving Show
data Dept    a = D [Unit a] deriving Show
data Unit    a = PU String | DU (Dept a) deriving Show

data CompanyU :: (* -> *) -> * where
    Company :: CompanyU Company
    Dept    :: CompanyU Dept
    Unit    :: CompanyU Unit

type ListOf = Comp (I []) ListU []
type instance PF CompanyU = ListOf (I Dept)         :>: Company
                        :+: ListOf (I Unit)         :>: Dept
                        :+: ( K String :+: I Dept ) :>: Unit

instance Ix CompanyU Company where
    from_ (C ds) = L (Tag (Comp (I (I0F (map (I . I0F) ds)))))
    to_ (L (Tag (Comp (I (I0F ds))))) = C (map (unI0F . unI) ds)
    index = Company

instance Ix CompanyU Dept where
    from_ (D us) = R (L (Tag (Comp (I (I0F (map (I . I0F) us))))))
    to_ (R (L (Tag (Comp (I (I0F us)))))) = D (map (unI0F . unI) us)
    index = Dept

instance Ix CompanyU Unit where
    from_ (PU s) = R (R (Tag (L (K s))))
    from_ (DU d) = R (R (Tag (R (I (I0F d)))))
    to_ (R (R (Tag (L (K s))))) = PU s
    to_ (R (R (Tag (R (I (I0F d)))))) = DU d
    index = Unit

c :: Company ()
c = C [D [PU "test", DU (D [])], D [DU (D []), PU "me"]]

c' :: Company ()
c' = f Company c
  where
    f :: Ix CompanyU ix => CompanyU ix -> ix e -> ix e
    f Unit = \u -> case u of (PU s) -> PU (map toUpper s); d -> d
    f Dept = \(D us) -> D (reverse (map (f Unit) us))
    f _ = compos f
