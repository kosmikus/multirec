module IndexFix where

open import Data.Bool
open import Data.Nat hiding (fold; _≟_)
open import Data.Sum
open import Data.Product
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Data.List renaming (map to lmap)
open import Data.Unit
open import Data.String using (String; _≟_)
open import Data.Empty
open import Data.Maybe
open import Data.Function
open import Category.Functor
open import Category.Monad
open import Data.Fin hiding (fold; _+_)
open import Data.Star hiding (map; fold; _>>=_; gmap; return)
open import Relation.Binary

module Base (n m : ℕ) where

  Ix = Fin n
  EIx = Fin m

  data Code : Set1 where
    I    :  Ix             -> Code
    E    :  EIx            -> Code
    K    :  Set            -> Code
    _⊕_  :  Code -> Code   -> Code
    _⊗_  :  Code -> Code   -> Code
    _▷_  :  Code -> Ix     -> Code

  infixr 6 _⊗_
  infixr 4 _⊕_
  infix  5 _▷_

  ⟦_⟧ : Code -> (Ix -> (EIx -> Set) -> Set) -> (EIx -> Set) -> Ix -> Set
  ⟦  I x      ⟧  ⟨_⟩  elem _  =  ⟨ x ⟩ elem
  ⟦  E x      ⟧  _    elem _  =  elem x
  ⟦  K A      ⟧  _    _    _  =  A
  ⟦  C₁ ⊕ C₂  ⟧  ⟨_⟩  elem y  =  ⟦ C₁ ⟧ ⟨_⟩ elem y  ⊎  ⟦  C₂  ⟧ ⟨_⟩ elem y
  ⟦  C₁ ⊗ C₂  ⟧  ⟨_⟩  elem y  =  ⟦ C₁ ⟧ ⟨_⟩ elem y  ×  ⟦  C₂  ⟧ ⟨_⟩ elem y
  ⟦  C ▷ x    ⟧  ⟨_⟩  elem y  =  x ≡ y         ×  ⟦  C   ⟧ ⟨_⟩ elem y

  map :   {F G : Ix -> (EIx -> Set) -> Set} {y : Ix} -> (C : Code) ->
          ({x : Ix} {elem : EIx -> Set} -> F x elem -> G x elem) -> (elem : EIx -> Set) -> ⟦ C ⟧ F elem y -> ⟦ C ⟧ G elem y
  map (  I x      )  f  _    y             =  f y
  map (  E x      )  f  _    y             =  y
  map (  K _      )  f  _    y             =  y
  map (  C₁ ⊕ C₂  )  f  elem (inj₁ y₁)     =  inj₁ (map C₁ f elem y₁)
  map (  C₁ ⊕ C₂  )  f  elem (inj₂ y₂)     =  inj₂ (map C₂ f elem y₂)
  map (  C₁ ⊗ C₂  )  f  elem (y₁ , y₂)     =  map C₁ f elem y₁ , map C₂ f elem y₂
  map (  C ▷ x    )  f  elem (≡-refl , y)  =  ≡-refl , map C f elem y

  record Fam : Set1 where
    field
      FC    :  Code
      ⟨_⟩   :  Ix -> (EIx -> Set) -> Set
      from  :  {x : Ix} {elem : EIx -> Set} -> ⟨ x ⟩ elem -> ⟦ FC ⟧ ⟨_⟩ elem x
      to    :  {x : Ix} {elem : EIx -> Set} -> ⟦ FC ⟧ ⟨_⟩ elem  x -> ⟨ x ⟩ elem

module List where

  open Base 1 1

  list  =  zero

  data L (A : Set) : Set where
    nil  : L A
    cons : A -> L A -> L A

  ListC  :  Code
  ListC =  (K ⊤  ⊕  E zero ⊗ I list) ▷ list

  ListI : Ix -> (EIx -> Set) -> Set
  ListI zero elem = List (elem zero)
  ListI (suc ()) _

  fromList : {x : Ix} {elem : EIx -> Set} -> ListI x elem -> ⟦ ListC ⟧ ListI elem x
  fromList {zero}    []       = ≡-refl , inj₁ _
  fromList {zero}    (x ∷ xs) = ≡-refl , inj₂ (x , xs)
  fromList {suc ()}  _

  toList : {x : Ix} {elem : EIx -> Set} -> ⟦ ListC ⟧ ListI elem x -> ListI x elem
  toList {zero}    (≡-refl , inj₁ _)        = []
  toList {zero}    (≡-refl , inj₂ (x , xs)) = x ∷ xs
  toList {suc ()}  _

  LF : Fam
  LF = record
           {  FC    =  ListC
           ;  ⟨_⟩   =  ListI
           ;  from  =  fromList
           ;  to    =  toList
           }

module Map {m n : ℕ} (F : Base.Fam m n) where

  open Base m n public
  open Fam F

  mutual
    map' : (C : Code) -> {elems₁ elems₂ : EIx -> Set} -> {x : Ix} ->
           ((ix : EIx) -> elems₁ ix -> elems₂ ix) -> ⟦ C ⟧ ⟨_⟩ elems₁ x -> ⟦ C ⟧ ⟨_⟩ elems₂ x
    map' (I n) {elems₁} {elems₂} f i             =  gmap elems₁ elems₂ f i
    map' (E n)                   f x             =  f n x
    map' (K A)                   _ x             =  x
    map' (F ⊕ G)                 f (inj₁ x)      =  inj₁ (map' F f x)
    map' (F ⊕ G)                 f (inj₂ x)      =  inj₂ (map' G f x)
    map' (F ⊗ G)                 f (x , y)       =  map' F f x , map' G f y
    map' (C ▷ n)                 f (≡-refl , x)  =  ≡-refl , map' C f x

    gmap : {x : Ix} -> (elems₁ elems₂ : EIx -> Set) -> ((ix : EIx) -> elems₁ ix -> elems₂ ix) -> ⟨ x ⟩ elems₁ -> ⟨ x ⟩ elems₂
    gmap {n} elems₁ elems₂ f x = to {n} {elems₂} (map' FC {elems₁} {elems₂} f (from {n} {elems₁} x))

module MapListTest where
  open List
  open Map LF
  open Fam LF
  isEven : ℕ -> Bool
  isEven 0             = true
  isEven 1             = false
  isEven (suc (suc n)) = isEven n

  test : gmap (const₁ ℕ) (const₁ Bool) (const isEven) (1 ∷ 2 ∷ 3 ∷ []) ≡ false ∷ true ∷ false ∷ []
  test = ≡-refl

module AST where

  Var  :  Set
  Var  =  String

  mutual
    data Expr : Set where
      econst  :  ℕ             -> Expr
      eadd    :  Expr -> Expr  -> Expr
      emul    :  Expr -> Expr  -> Expr
      evar    :  Var           -> Expr
      elet    :  Decl -> Expr  -> Expr

    data Decl : Set where
      _≔_     :  Var -> Expr   -> Decl
      _∙_     :  Decl -> Decl  -> Decl

  infixr 3 _≔_
  infixl 2 _∙_

  open Base 3 0

  expr  =  zero
  decl  =  suc zero
  var   =  suc (suc zero)

  data ViewAST : Ix -> Set where
    vexpr  :  ViewAST expr
    vdecl  :  ViewAST decl
    vvar   :  ViewAST var
  
  viewAST : (n : Ix) -> ViewAST n
  viewAST zero                  =  vexpr
  viewAST (suc zero)            =  vdecl
  viewAST (suc (suc zero))      =  vvar
  viewAST (suc (suc (suc ())))  --

  ExprC  :  Code
  ExprC  =  K ℕ                  -- |econst|
         ⊕  I expr  ⊗  I expr    -- |eadd|
         ⊕  I expr  ⊗  I expr    -- |emul|
         ⊕  I var                -- |evar|
         ⊕  I decl  ⊗  I expr    -- |elet|
  
  DeclC  :  Code
  DeclC  =  I var   ⊗  I expr    -- |_≔_|
         ⊕  I decl  ⊗  I decl    -- |_∙_|

  VarC   :  Code
  VarC   =  K String
  
  ASTC   :  Code
  ASTC   =  ExprC  ▷  expr
         ⊕  DeclC  ▷  decl
         ⊕  VarC   ▷  var

  AST⟨_⟩ : Ix -> (EIx -> Set) -> Set
  AST⟨  x      ⟩ _ with viewAST x
  AST⟨  (. _)  ⟩ _ | vexpr  =  Expr
  AST⟨  (. _)  ⟩ _ | vdecl  =  Decl
  AST⟨  (. _)  ⟩ _ | vvar   =  Var

  fromExpr : Expr -> ⟦ ExprC ⟧ AST⟨_⟩ (\()) expr
  fromExpr  (econst i       )  =  inj₁                    i
  fromExpr  (eadd   e₁  e₂  )  =  inj₂ (inj₁              (e₁  ,  e₂  )  )
  fromExpr  (emul   e₁  e₂  )  =  inj₂ (inj₂ (inj₁        (e₁  ,  e₂  )  ))
  fromExpr  (evar   v       )  =  inj₂ (inj₂ (inj₂ (inj₁  v              )))
  fromExpr  (elet   d   e   )  =  inj₂ (inj₂ (inj₂ (inj₂  (d   ,  e   )  )))
  
  fromDecl : Decl -> ⟦ DeclC ⟧ AST⟨_⟩ (\()) decl
  fromDecl  (v   ≔   e   )   =  inj₁  (v , e)
  fromDecl  (d₁  ∙   d₂  )   =  inj₂  (d₁ , d₂)

  fromVar : Var -> ⟦ VarC ⟧ AST⟨_⟩ (\()) var
  fromVar v = v
  
  fromAST : {x : Ix} {elem : EIx -> Set} -> AST⟨ x ⟩ elem -> ⟦ ASTC ⟧ AST⟨_⟩ elem x
  fromAST {x} v with viewAST x
  fromAST e  |  vexpr  =  inj₁          (≡-refl , fromExpr   e  ) 
  fromAST d  |  vdecl  =  inj₂ (inj₁    (≡-refl , fromDecl   d  ))
  fromAST v  |  vvar   =  inj₂ (inj₂    (≡-refl , fromVar    v  ))

  toExpr : ⟦ ExprC ⟧ AST⟨_⟩ (\()) expr -> Expr
  toExpr (inj₁                    i              )     =  econst i
  toExpr (inj₂ (inj₁              (e₁  ,  e₂  )  ))    =  eadd e₁ e₂
  toExpr (inj₂ (inj₂ (inj₁        (e₁  ,  e₂  )  )))   =  emul e₁ e₂
  toExpr (inj₂ (inj₂ (inj₂ (inj₁  v              ))))  =  evar v
  toExpr (inj₂ (inj₂ (inj₂ (inj₂  (d   ,  e   )  ))))  =  elet d e

  toDecl : ⟦ DeclC ⟧ AST⟨_⟩ (\()) decl -> Decl
  toDecl (inj₁  (v    ,  e   ))  =  v   ≔   e
  toDecl (inj₂  (d₁   ,  d₂  ))  =  d₁  ∙   d₂

  toVar : ⟦ VarC ⟧ AST⟨_⟩ (\()) var -> Var
  toVar v = v

  toAST : {x : Ix} {elem : EIx -> Set} -> ⟦ ASTC ⟧ AST⟨_⟩ elem x -> AST⟨ x ⟩ elem
  toAST (inj₁        (≡-refl  ,    e  ))   =   toExpr e
  toAST (inj₂ (inj₁  (≡-refl  ,    d  )))  =   toDecl d
  toAST (inj₂ (inj₂  (≡-refl  ,    v  )))  =   toVar v

  AST : Fam
  AST = record
          {  FC    =  ASTC
          ;  ⟨_⟩   =  AST⟨_⟩
          ;  from  =  fromAST
          ;  to    =  toAST
          }

module Fold {m n : ℕ} (F : Base.Fam m n) where

  open Base m n public
  open Fam F

  RawAlg : Code -> (F G : Ix -> (EIx -> Set) -> Set) -> Ix -> (EIx -> Set) -> Set
  RawAlg C F G y elem = ⟦ C ⟧ F elem y -> G y elem

  Alg : Code -> (F G : Ix -> (EIx -> Set) -> Set) -> Ix -> (EIx -> Set) -> Set
  Alg (  I x      )  F G y elem =  F x elem -> G y elem
  Alg (  E n      )  F G y elem =  elem n -> G y elem
  Alg (  K A      )  F G y elem =  A -> G y elem
  Alg (  C₁ ⊕ C₂  )  F G y elem =  Alg C₁ F G y elem × Alg C₂ F G y elem
  Alg (  C₁ ⊗ C₂  )  F G y elem =  Alg C₁ F (Alg C₂ F G) y elem
  Alg (  C ▷ x    )  F G y elem =  Alg C F G x elem

  RawAlgebra   : (Ix -> (EIx -> Set) -> Set) -> Set1
  RawAlgebra  F  =  (x : Ix) (elem : EIx -> Set) -> RawAlg  FC F F x elem

  Algebra      : (Ix -> (EIx -> Set) -> Set) -> Set1
  Algebra     F  =  (x : Ix) (elem : EIx -> Set) -> Alg     FC F F x elem

  apply :   (C : Code) {elem : EIx -> Set} {F G : Ix -> (EIx -> Set) -> Set} {y : Ix} ->
            Alg C F G y elem -> RawAlg C F G y elem
  apply (  I x      )  a          y             =  a y
  apply (  E n      )  a          y             =  a y
  apply (  K _      )  a          y             =  a y
  apply (  C₁ ⊕ C₂  )  (a₁ , a₂)  (inj₁ y₁)     =  apply C₁ a₁ y₁
  apply (  C₁ ⊕ C₂  )  (a₁ , a₂)  (inj₂ y₂)     =  apply C₂ a₂ y₂
  apply (  C₁ ⊗ C₂  )  a          (y₁ , y₂)     =  apply C₂ (apply C₁ a y₁) y₂
  apply (  C ▷ x    )  a          (≡-refl , y)  =  apply C a y

  -- does not termination-check:
  foldRaw   :  {y : Ix} {elem : EIx -> Set} {F : Ix -> (EIx -> Set) -> Set} -> 
               RawAlgebra F  ->  ⟨ y ⟩ elem -> F y elem

  foldRaw {y} {elem} alg x = alg _ elem (map FC (foldRaw  alg) elem (from {y} {elem} x))

  fold      :  {y : Ix} {elem : EIx -> Set} {F : Ix -> (EIx -> Set) -> Set} ->
               Algebra     F  ->  ⟨ y ⟩ elem -> F y elem

  fold alg = foldRaw (\ x elem -> apply FC (alg x elem))

module FoldExample where

  open AST
  open Fold  AST
  open Fam   AST

  Env : Set
  Env = Var -> ℕ

  empty : Env
  empty _ = 0

  insert : Var -> ℕ -> Env -> Env
  insert x v env y with decToBool (x ≟ y)
  ... | true  = v
  ... | false = env y

  testInsert₁ : (insert "x" 2 empty) "x" ≡ 2
  testInsert₁ = ≡-refl

  testInsert₂ : (insert "x" 4 (insert "x" 2 empty)) "x" ≡ 4
  testInsert₂ = ≡-refl

  testInsert₃ : (insert "y" 4 (insert "x" 2 empty)) "x" ≡ 2
  testInsert₃ = ≡-refl

  Value : Ix -> (EIx -> Set) -> Set
  Value x _ with viewAST x
  Value (. _) _ | vexpr  =  Env -> ℕ
  Value (. _) _ | vdecl  =  Env -> Env
  Value (. _) _ | vvar   =  Var

  evalAlgebra : Algebra Value
  evalAlgebra _ _ =
                   (  (\ i       env  ->  i                     )   ,   -- |econst|
                      (\ r₁  r₂  env  ->  r₁ env + r₂ env       )   ,   -- |eadd|
                      (\ r₁  r₂  env  ->  r₁ env * r₂ env       )   ,   -- |emul|
                      (\ v       env  ->  env v                 )   ,   -- |evar|
                      (\ f   r   env  ->  r (f env)             ))  ,   -- |elet|
                   (  (\ v   r   env  ->  insert v (r env) env  )   ,   -- |_≔_|
                      (\ f₁  f₂  env  ->  f₂ (f₁ env)           ))  ,   -- |_∙_|
                   (  (\ v            ->  v                     ))

  eval : Expr -> Value expr (\())
  eval = fold {expr} {\()} {Value} evalAlgebra

  example : Expr
  example = elet  (  "x"  ≔  emul (econst 6) (econst 9) ∙
                     "y"  ≔  eadd (evar "x") (econst 2))
                  (eadd (evar "y") (evar "x"))

  testFold : eval example empty ≡ 110
  testFold = ≡-refl

module Zipper {m n : ℕ} (F : Base.Fam m n) (elem : Fin n -> Set) where

  open Base m n public
  open Fam F

  infixr 1 _,_

  Ctx : Code -> Ix -> Ix -> Set
  Ctx (  I x      )  y z  =  x ≡ y
  Ctx (  E n      )  y z  =  ⊥
  Ctx (  K _      )  y z  =  ⊥
  Ctx (  C₁ ⊕ C₂  )  y z  =  Ctx C₁ y z    ⊎  Ctx C₂ y z
  Ctx (  C₁ ⊗ C₂  )  y z  =  Ctx C₁ y z    ×  ⟦ C₂ ⟧ ⟨_⟩ elem z
                          ⊎  ⟦ C₁ ⟧ ⟨_⟩ elem z  ×  Ctx C₂ y z
  Ctx (  C ▷ x    )  y z  =  x ≡ z × Ctx C y z
  Ctxs : Rel Ix
  Ctxs = Star (Ctx FC)

  data Loc : Ix -> Set where
    _,_ : {x y : Ix} -> ⟨ x ⟩ elem -> Ctxs x y -> Loc y

  fill :   (C : Code) {x y : Ix} -> 
           Ctx C x y -> ⟨ x ⟩ elem -> ⟦ C ⟧ ⟨_⟩ elem y
  fill (  I _      )   ≡-refl                 y   =  y
  fill (  E _      )   ()                     _
  fill (  K _      )   ()                     _ 
  fill (  C₁ ⊕ C₂  )   (inj₁ cy₁)             y₁  =  inj₁ (fill C₁ cy₁ y₁)
  fill (  C₁ ⊕ C₂  )   (inj₂ cy₂)             y₂  =  inj₂ (fill C₂ cy₂ y₂)
  fill (  C₁ ⊗ C₂  )   (inj₁ (cy₁ , y₂))      y₁  =  fill C₁ cy₁ y₁ , y₂
  fill (  C₁ ⊗ C₂  )   (inj₂ (y₁ , cy₂))      y₂  =  y₁ , fill C₂ cy₂ y₂
  fill (  C ▷ _    )   (≡-refl , cy)          y   =  ≡-refl , fill C cy y

  open RawMonadPlus MaybeMonadPlus

  Nav : Set
  Nav = {x : Ix} -> Loc x -> Maybe (Loc x)

  up : Nav
  up (x , ε)       =  ∅
  up (x , c ◅ cs)  =  return (to (fill FC c x) , cs)

  first :   {A : Set} (C : Code) {y : Ix} ->
            ({x : Ix} -> ⟨ x ⟩ elem -> Ctx C x y -> A) ->
            ⟦ C ⟧ ⟨_⟩ elem y -> Maybe A
  first (  I _      ) k y             =  return (k y ≡-refl)
  first (  E _      ) k _             =  ∅
  first (  K _      ) k _             =  ∅
  first (  C₁ ⊕ C₂  ) k (inj₁ y₁)     =  first C₁  (\z cy₁  ->  k z (inj₁ cy₁)         )  y₁
  first (  C₁ ⊕ C₂  ) k (inj₂ y₂)     =  first C₂  (\z cy₂  ->  k z (inj₂ cy₂)         )  y₂
  first (  C₁ ⊗ C₂  ) k (y₁ , y₂)     =  first C₁  (\z cy₁  ->  k z (inj₁ (cy₁ , y₂))  )  y₁
                                      ∣  first C₂  (\z cy₂  ->  k z (inj₂ (y₁ , cy₂))  )  y₂
  first (  C ▷ _    ) k (≡-refl , y)  =  first C   (\z cy   ->  k z (≡-refl , cy)      )  y

  down : Nav
  down (x , cs) = first FC (\z c -> z , (c ◅ cs)) (from x)

  next :   {A : Set} (C : Code) {y : Ix} ->
           ({x : Ix} -> ⟨ x ⟩ elem -> Ctx C x y -> A) ->
           {x : Ix} -> Ctx C x y -> ⟨ x ⟩ elem -> Maybe A
  next (  I _      ) k ≡-refl             y   =  ∅
  next (  E _      ) k ()                 _
  next (  K _      ) k ()                 _
  next (  C₁ ⊕ C₂  ) k (inj₁ cy₁)         y₁  =  next   C₁  (\z cy₁′  -> k z (inj₁ cy₁′)                         ) cy₁  y₁
  next (  C₁ ⊕ C₂  ) k (inj₂ cy₂)         y₂  =  next   C₂  (\z cy₂′  -> k z (inj₂ cy₂′)                         ) cy₂  y₂
  next (  C₁ ⊗ C₂  ) k (inj₁ (cy₁ , y₂))  y₁  =  next   C₁  (\z cy₁′  -> k z (inj₁ (cy₁′            ,  y₂    ))  ) cy₁  y₁
                                              ∣  first  C₂  (\z cy₁′  -> k z (inj₂ (fill C₁ cy₁ y₁  ,  cy₁′  ))  )      y₂
  next (  C₁ ⊗ C₂  ) k (inj₂ (y₁ , cy₂))  y₂  =  next   C₂  (\z cy₂′  -> k z (inj₂ (y₁              ,  cy₂′  ))  ) cy₂  y₂
  next (  C ▷ _    ) k (≡-refl , cy)      y   =  next   C   (\z cy′   -> k z (≡-refl , cy′)                      ) cy   y

  right : Nav
  right (x ,  ε         )  =  ∅
  right (x ,  (c ◅ cs)  )  =  next FC (\z c′ -> z , (c′ ◅ cs)) c x

  enter : {x : Ix} -> ⟨ x ⟩ elem -> Loc x
  enter x = x , ε

  leave : {x : Ix} -> Loc x -> ⟨ x ⟩ elem
  leave (x , ε)         =  x
  leave (x , (c ◅ cs))  =  leave (to (fill FC c x) , cs)

  update : ((x : Ix) -> ⟨ x ⟩ elem -> ⟨ x ⟩ elem ) -> Nav
  update f (x , cs) = return (f _ x , cs)

  on :  {A : Set} -> ((x : Ix) -> ⟨ x ⟩ elem -> A) ->
        {x : Ix} -> Loc x -> A
  on f (x , cs) = f _ x

module ZipperExample where

  open AST
  open Zipper AST (\())
  open Fam AST
  open FoldExample
  open RawMonadPlus MaybeMonadPlus

  source : Expr
  source = elet  ("x" ≔ emul (econst 6) (econst 9)) 
                 (eadd (evar "x") (evar "y"))

  callZipper : Maybe Expr
  callZipper =
    return (enter {expr} source) >>=
    down >>= down >>= right >>= update simp >>=
    return ∘ leave
      where  simp : {elem : EIx -> Set} (n : Ix) -> ⟨ n ⟩ elem -> ⟨ n ⟩ elem
             simp n x with viewAST n
             simp (. _) e  |  vexpr  =  econst (eval e empty)
             simp (. _) d  |  vdecl  =  d
             simp (. _) v  |  vvar   =  v

  target = elet ("x" ≔ econst 54) (eadd (evar "x") (evar "y"))
  testZipper : callZipper ≡ just target
  testZipper = ≡-refl