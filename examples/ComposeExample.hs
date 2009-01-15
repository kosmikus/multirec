{-# LANGUAGE GADTs
           , TypeFamilies
           , TypeOperators
           , KindSignatures
           , MultiParamTypeClasses
           , FlexibleContexts
           #-}
module BaseFExample where

import Data.Char (toUpper)
import Generics.MultiRec.Base hiding (C)
import qualified Generics.MultiRec.BaseF as F
import Generics.MultiRec.HFunctor
import Generics.MultiRec.Compos

import ListRep

data Company = C [Dept] deriving Show
data Dept    = D [Unit] deriving Show
data Unit    = PU String | DU Dept deriving Show

data CompanyU :: * -> * where
    Company :: CompanyU Company
    Dept    :: CompanyU Dept
    Unit    :: CompanyU Unit

type instance PF CompanyU = ListOf (I Dept)         :>: Company
                        :+: ListOf (I Unit)         :>: Dept
                        :+: ( K String :+: I Dept ) :>: Unit

instance Ix CompanyU Company where
    from_ (C ds) = L (Tag (Comp (F.I (I0F (map (I . I0) ds)))))
    to_ (L (Tag (Comp (F.I (I0F ds))))) = C (map (unI0 . unI) ds)
    index = Company

instance Ix CompanyU Dept where
    from_ (D us) = R (L (Tag (Comp (F.I (I0F (map (I . I0) us))))))
    to_ (R (L (Tag (Comp (F.I (I0F us)))))) = D (map (unI0 . unI) us)
    index = Dept

instance Ix CompanyU Unit where
    from_ (PU s) = R (R (Tag (L (K s))))
    from_ (DU d) = R (R (Tag (R (I (I0 d)))))
    to_ (R (R (Tag (L (K s))))) = PU s
    to_ (R (R (Tag (R (I (I0 d)))))) = DU d
    index = Unit

c :: Company
c = C [D [PU "test", DU (D [])], D [DU (D []), PU "me"]]

c' :: Company
c' = f Company c
  where
    f :: Ix CompanyU ix => CompanyU ix -> ix -> ix
    f Unit = \u -> case u of (PU s) -> PU (map toUpper s); d -> d
    f Dept = \(D us) -> D (reverse (map (f Unit) us))
    f _ = compos f
