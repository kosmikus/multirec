{-# LANGUAGE GADTs
           , KindSignatures
           , MultiParamTypeClasses
           , TypeFamilies
           , TypeOperators
           , FlexibleInstances
           #-}
module CompanyReps where

import Generics.MultiRec hiding (C)
import qualified Generics.MultiRec as MR
import CompanyDatatypes

data CompanyU :: * -> * where
    Company  :: CompanyU Company
    DeptList :: CompanyU [Dept]
    Dept     :: CompanyU Dept
    UnitList :: CompanyU [Unit]
    Unit     :: CompanyU Unit
    Employee :: CompanyU Employee
    Person   :: CompanyU Person
    Salary   :: CompanyU Salary

type instance PF CompanyU = I [Dept] :>: Company
                   :+: (K ()) :>: [Dept]
                   :+: (I Dept :*: I [Dept]) :>: [Dept]
                   :+: (K String :*: I Employee :*: I [Unit]) :>: Dept
                   :+: (K ()) :>: [Unit]
                   :+: (I Unit :*: I [Unit]) :>: [Unit]
                   :+: I Employee :>: Unit
                   :+: I Dept :>: Unit
                   :+: (I Person :*: I Salary) :>: Employee
                   :+: (K String :*: K String) :>: Person
                   :+: K Float :>: Salary

instance Ix CompanyU Company where
    from_ (C ds) = L (Tag (I (I0 ds)))
    to_ (L (Tag (I (I0 ds)))) = C ds
    index = Company

instance Ix CompanyU [Dept] where
    from_ [] = R (L (Tag (K ())))
    from_ (d : ds) = R (R (L (Tag (I (I0 d) :*: I (I0 ds)))))
    to_ (R (L (Tag (K ())))) = []
    to_ (R (R (L (Tag (I (I0 d) :*: I (I0 ds)))))) = d : ds
    index = DeptList

instance Ix CompanyU Dept where
    from_ (D n m us) = R (R (R (L (Tag (K n :*: I (I0 m) :*: I (I0 us))))))
    to_ (R (R (R (L (Tag (K n :*: I (I0 m) :*: I (I0 us))))))) = D n m us
    index = Dept

instance Ix CompanyU [Unit] where
    from_ [] = R (R (R (R (L (Tag (K ()))))))
    from_ (u : us) = R (R (R (R (R (L (Tag (I (I0 u) :*: I (I0 us))))))))
    to_ (R (R (R (R (L (Tag (K ()))))))) = []
    to_ (R (R (R (R (R (L (Tag (I (I0 u) :*: I (I0 us))))))))) = u : us
    index = UnitList

instance Ix CompanyU Unit where
    from_ (PU e) = R (R (R (R (R (R (L (Tag (I (I0 e)))))))))
    from_ (DU d) = R (R (R (R (R (R (R (L (Tag (I (I0 d))))))))))
    to_ (R (R (R (R (R (R (L (Tag (I (I0 e)))))))))) = PU e
    to_ (R (R (R (R (R (R (R (L (Tag (I (I0 d))))))))))) = DU d
    index = Unit

instance Ix CompanyU Employee where
    from_ (E p s) = R (R (R (R (R (R (R (R (L (Tag (I (I0 p) :*: I (I0 s)))))))))))
    to_ (R (R (R (R (R (R (R (R (L (Tag (I (I0 p) :*: I (I0 s)))))))))))) = E p s
    index = Employee

instance Ix CompanyU Person where
    from_ (P n a) = R (R (R (R (R (R (R (R (R (L (Tag (K n :*: K a)))))))))))
    to_ (R (R (R (R (R (R (R (R (R (L (Tag (K n :*: K a)))))))))))) = P n a
    index = Person

instance Ix CompanyU Salary where
    from_ (S s) = R (R (R (R (R (R (R (R (R (R (Tag (K s)))))))))))
    to_ (R (R (R (R (R (R (R (R (R (R (Tag (K s)))))))))))) = S s
    index = Salary

instance Eq_ CompanyU where
    eq_ Company Company = Just Refl
    eq_ DeptList DeptList = Just Refl
    eq_ Dept Dept = Just Refl
    eq_ UnitList UnitList = Just Refl
    eq_ Unit Unit = Just Refl
    eq_ Employee Employee = Just Refl
    eq_ Person Person = Just Refl
    eq_ Salary Salary = Just Refl
    eq_ _ _ = Nothing
