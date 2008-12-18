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
open import Data.Star hiding (map; fold; _>>=_)
                      renaming (ε to []; _◅_ to _∷_;
                                return to [_])
open import Relation.Binary

module Base (n : ℕ) where

  Ix = Fin n

  data Code : Set1 where
    I    :  Ix             -> Code
    K    :  Set            -> Code
    _⊕_  :  Code -> Code   -> Code
    _⊗_  :  Code -> Code   -> Code
    _▷_  :  Code -> Ix     -> Code

  infixr 6 _⊗_
  infixr 4 _⊕_
  infix  5 _▷_

  ⟦_⟧ : Code -> (Ix -> Set) -> Ix -> Set
  ⟦  I x      ⟧  ⟨_⟩  _  =  ⟨ x ⟩
  ⟦  K A      ⟧  _    _  =  A
  ⟦  C₁ ⊕ C₂  ⟧  ⟨_⟩  y  =  ⟦ C₁ ⟧ ⟨_⟩ y  ⊎  ⟦  C₂  ⟧ ⟨_⟩ y
  ⟦  C₁ ⊗ C₂  ⟧  ⟨_⟩  y  =  ⟦ C₁ ⟧ ⟨_⟩ y  ×  ⟦  C₂  ⟧ ⟨_⟩ y
  ⟦  C ▷ x    ⟧  ⟨_⟩  y  =  x ≡ y         ×  ⟦  C   ⟧ ⟨_⟩ y

  map :   {F G : Ix -> Set} {y : Ix} -> (C : Code) ->
          ({x : Ix} -> F x -> G x) -> ⟦ C ⟧ F y -> ⟦ C ⟧ G y
  map (  I x      )  f  y             =  f y
  map (  K _      )  f  y             =  y
  map (  C₁ ⊕ C₂  )  f  (inj₁ y₁)     =  inj₁ (map C₁ f y₁)
  map (  C₁ ⊕ C₂  )  f  (inj₂ y₂)     =  inj₂ (map C₂ f y₂)
  map (  C₁ ⊗ C₂  )  f  (y₁ , y₂)     =  map C₁ f y₁ , map C₂ f y₂
  map (  C ▷ x    )  f  (≡-refl , y)  =  ≡-refl , map C f y

  record Fam : Set1 where
    field
      FC    :  Code
      ⟨_⟩   :  Ix -> Set
      from  :  {x : Ix} -> ⟨ x ⟩ -> ⟦ FC ⟧ ⟨_⟩ x
      to    :  {x : Ix} -> ⟦ FC ⟧ ⟨_⟩ x -> ⟨ x ⟩

module List where

  open Base 2

  list  =  zero
  el    =  suc zero

  data L (A : Set) : Set where
    nil  : L A
    cons : A -> L A -> L A

  ListC  :  Code
  ListC =  (K ⊤ ⊕  I el    ⊗  I list) ▷ list
        ⊕  I el ▷ el

  ListI : Set -> Ix -> Set
  ListI A zero = List A
  ListI A (suc zero) = A
  ListI A (suc (suc ()))

  fromList : {x : Ix} -> {A : Set} -> ListI A x  -> ⟦ ListC ⟧ (ListI A) x
  fromList {zero} [] = inj₁ (≡-refl , inj₁ tt  ) 
  fromList {zero} (x ∷ xs) = inj₁ (≡-refl , inj₂ (x , xs)  ) 
  fromList {suc zero} a = inj₂ (≡-refl , a ) 
  fromList {suc (suc ())} _

  toList : {x : Ix} -> {A : Set} -> ⟦ ListC ⟧ (ListI A) x -> ListI A x
  toList (inj₁ (≡-refl , inj₁ tt)) = []
  toList (inj₁ (≡-refl , inj₂ (x , xs))) = x ∷ xs
  toList (inj₂ (≡-refl , a)) = a

  LF : Set -> Fam
  LF A = record
           {  FC    =  ListC
           ;  ⟨_⟩   =  ListI A
           ;  from  =  fromList {A = A}
           ;  to    =  toList {A = A}
           }

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

  open Base 3

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
  AST⟨_⟩ : Ix -> Set
  AST⟨  x      ⟩ with viewAST x
  AST⟨  (. _)  ⟩ | vexpr  =  Expr
  AST⟨  (. _)  ⟩ | vdecl  =  Decl
  AST⟨  (. _)  ⟩ | vvar   =  Var

  fromExpr : Expr -> ⟦ ExprC ⟧ AST⟨_⟩ expr
  fromExpr  (econst i       )  =  inj₁                    i
  fromExpr  (eadd   e₁  e₂  )  =  inj₂ (inj₁              (e₁  ,  e₂  )  )
  fromExpr  (emul   e₁  e₂  )  =  inj₂ (inj₂ (inj₁        (e₁  ,  e₂  )  ))
  fromExpr  (evar   v       )  =  inj₂ (inj₂ (inj₂ (inj₁  v              )))
  fromExpr  (elet   d   e   )  =  inj₂ (inj₂ (inj₂ (inj₂  (d   ,  e   )  )))
  
  fromDecl : Decl -> ⟦ DeclC ⟧ AST⟨_⟩ decl
  fromDecl  (v   ≔   e   )   =  inj₁  (v , e)
  fromDecl  (d₁  ∙   d₂  )   =  inj₂  (d₁ , d₂)

  fromVar : Var -> ⟦ VarC ⟧ AST⟨_⟩ var
  fromVar v = v
  
  fromAST : {x : Ix} -> AST⟨ x ⟩ -> ⟦ ASTC ⟧ AST⟨_⟩ x
  fromAST {x} v with viewAST x
  fromAST e  |  vexpr  =  inj₁          (≡-refl , fromExpr   e  ) 
  fromAST d  |  vdecl  =  inj₂ (inj₁    (≡-refl , fromDecl   d  ))
  fromAST v  |  vvar   =  inj₂ (inj₂    (≡-refl , fromVar    v  ))

  toExpr : ⟦ ExprC ⟧ AST⟨_⟩ expr -> Expr
  toExpr (inj₁                    i              )     =  econst i
  toExpr (inj₂ (inj₁              (e₁  ,  e₂  )  ))    =  eadd e₁ e₂
  toExpr (inj₂ (inj₂ (inj₁        (e₁  ,  e₂  )  )))   =  emul e₁ e₂
  toExpr (inj₂ (inj₂ (inj₂ (inj₁  v              ))))  =  evar v
  toExpr (inj₂ (inj₂ (inj₂ (inj₂  (d   ,  e   )  ))))  =  elet d e

  toDecl : ⟦ DeclC ⟧ AST⟨_⟩ decl -> Decl
  toDecl (inj₁  (v    ,  e   ))  =  v   ≔   e
  toDecl (inj₂  (d₁   ,  d₂  ))  =  d₁  ∙   d₂

  toVar : ⟦ VarC ⟧ AST⟨_⟩ var -> Var
  toVar v = v

  toAST : {x : Ix} -> ⟦ ASTC ⟧ AST⟨_⟩ x -> AST⟨ x ⟩
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

module Fold {n : ℕ} (F : Base.Fam n) where

  open Base n public
  open Fam F

  RawAlg : Code -> (F G : Ix -> Set) -> Ix -> Set
  RawAlg C F G y = ⟦ C ⟧ F y -> G y

  Alg : Code -> (F G : Ix -> Set) -> Ix -> Set
  Alg (  I x      )  F G y  =  F x -> G y
  Alg (  K A      )  F G y  =  A -> G y
  Alg (  C₁ ⊕ C₂  )  F G y  =  Alg C₁ F G y × Alg C₂ F G y
  Alg (  C₁ ⊗ C₂  )  F G y  =  Alg C₁ F (Alg C₂ F G) y
  Alg (  C ▷ x    )  F G y  =  Alg C F G x

  RawAlgebra   : (Ix -> Set) -> Set
  RawAlgebra  F  =  (x : Ix) -> RawAlg  FC F F x

  Algebra      : (Ix -> Set) -> Set
  Algebra     F  =  (x : Ix) -> Alg     FC F F x

  apply :   (C : Code) {F G : Ix -> Set} {y : Ix} ->
            Alg C F G y -> RawAlg C F G y
  apply (  I x      )  a          y             =  a y
  apply (  K _      )  a          y             =  a y
  apply (  C₁ ⊕ C₂  )  (a₁ , a₂)  (inj₁ y₁)     =  apply C₁ a₁ y₁
  apply (  C₁ ⊕ C₂  )  (a₁ , a₂)  (inj₂ y₂)     =  apply C₂ a₂ y₂
  apply (  C₁ ⊗ C₂  )  a          (y₁ , y₂)     =  apply C₂ (apply C₁ a y₁) y₂
  apply (  C ▷ x    )  a          (≡-refl , y)  =  apply C a y

  -- does not termination-check:
  foldRaw   :  {y : Ix} {F : Ix -> Set} -> 
               RawAlgebra  F  ->  ⟨ y ⟩ -> F y

  foldRaw alg x = alg _ (map FC (foldRaw  alg) (from x))

  fold      :  {y : Ix} {F : Ix -> Set} ->
               Algebra     F  ->  ⟨ y ⟩ -> F y

  fold alg = foldRaw (\ x -> apply FC (alg x))

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

  Value : Ix -> Set
  Value x with viewAST x
  Value (. _)  | vexpr  =  Env -> ℕ
  Value (. _)  | vdecl  =  Env -> Env
  Value (. _)  | vvar   =  Var

  evalAlgebra : Algebra Value
  evalAlgebra _ =  
                   (  (\ i       env  ->  i                     )   ,   -- |econst|
                      (\ r₁  r₂  env  ->  r₁ env + r₂ env       )   ,   -- |eadd|
                      (\ r₁  r₂  env  ->  r₁ env * r₂ env       )   ,   -- |emul|
                      (\ v       env  ->  env v                 )   ,   -- |evar|
                      (\ f   r   env  ->  r (f env)             ))  ,   -- |elet|
                   (  (\ v   r   env  ->  insert v (r env) env  )   ,   -- |_≔_|
                      (\ f₁  f₂  env  ->  f₂ (f₁ env)           ))  ,   -- |_∙_|
                   (  (\ v            ->  v                     ))
  eval : Expr -> Value expr
  eval = fold {expr} {Value} evalAlgebra

  example : Expr
  example = elet  (  "x"  ≔  emul (econst 6) (econst 9) ∙
                     "y"  ≔  eadd (evar "x") (econst 2))
                  (eadd (evar "y") (evar "x"))

  testFold : eval example empty ≡ 110
  testFold = ≡-refl

module Zipper {n : ℕ} (F : Base.Fam n) where

  open Base n public
  open Fam F

  infixr 1 _,_

  Ctx : Code -> Ix -> Ix -> Set
  Ctx (  I x      )  y z  =  x ≡ y
  Ctx (  K _      )  y z  =  ⊥
  Ctx (  C₁ ⊕ C₂  )  y z  =  Ctx C₁ y z    ⊎  Ctx C₂ y z
  Ctx (  C₁ ⊗ C₂  )  y z  =  Ctx C₁ y z    ×  ⟦ C₂ ⟧ ⟨_⟩ z
                          ⊎  ⟦ C₁ ⟧ ⟨_⟩ z  ×  Ctx C₂ y z
  Ctx (  C ▷ x    )  y z  =  x ≡ z × Ctx C y z
  Ctxs : Rel Ix
  Ctxs = Star (Ctx FC)

  data Loc : Ix -> Set where
    _,_ : {x y : Ix} -> ⟨ x ⟩ -> Ctxs x y -> Loc y

  fill :   (C : Code) {x y : Ix} -> 
           Ctx C x y -> ⟨ x ⟩ -> ⟦ C ⟧ ⟨_⟩ y
  fill (  I _      )   ≡-refl                 y   =  y
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
  up (x , [])      =  ∅
  up (x , c ∷ cs)  =  return (to (fill FC c x) , cs)

  first :   {A : Set} (C : Code) {y : Ix} ->
            ({x : Ix} -> ⟨ x ⟩ -> Ctx C x y -> A) ->
            ⟦ C ⟧ ⟨_⟩ y -> Maybe A
  first (  I _      ) k y             =  return (k y ≡-refl)
  first (  K _      ) k _             =  ∅
  first (  C₁ ⊕ C₂  ) k (inj₁ y₁)     =  first C₁  (\z cy₁  ->  k z (inj₁ cy₁)         )  y₁
  first (  C₁ ⊕ C₂  ) k (inj₂ y₂)     =  first C₂  (\z cy₂  ->  k z (inj₂ cy₂)         )  y₂
  first (  C₁ ⊗ C₂  ) k (y₁ , y₂)     =  first C₁  (\z cy₁  ->  k z (inj₁ (cy₁ , y₂))  )  y₁
                                      ∣  first C₂  (\z cy₂  ->  k z (inj₂ (y₁ , cy₂))  )  y₂
  first (  C ▷ _    ) k (≡-refl , y)  =  first C   (\z cy   ->  k z (≡-refl , cy)      )  y

  down : Nav
  down (x , cs) = first FC (\z c -> z , (c ∷ cs)) (from x) 

  next :   {A : Set} (C : Code) {y : Ix} ->
           ({x : Ix} -> ⟨ x ⟩ -> Ctx C x y -> A) ->
           {x : Ix} -> Ctx C x y -> ⟨ x ⟩ -> Maybe A
  next (  I _      ) k ≡-refl             y   =  ∅
  next (  K _      ) k ()                 _
  next (  C₁ ⊕ C₂  ) k (inj₁ cy₁)         y₁  =  next   C₁  (\z cy₁′  -> k z (inj₁ cy₁′)                         ) cy₁  y₁
  next (  C₁ ⊕ C₂  ) k (inj₂ cy₂)         y₂  =  next   C₂  (\z cy₂′  -> k z (inj₂ cy₂′)                         ) cy₂  y₂
  next (  C₁ ⊗ C₂  ) k (inj₁ (cy₁ , y₂))  y₁  =  next   C₁  (\z cy₁′  -> k z (inj₁ (cy₁′            ,  y₂    ))  ) cy₁  y₁
                                              ∣  first  C₂  (\z cy₁′  -> k z (inj₂ (fill C₁ cy₁ y₁  ,  cy₁′  ))  )      y₂
  next (  C₁ ⊗ C₂  ) k (inj₂ (y₁ , cy₂))  y₂  =  next   C₂  (\z cy₂′  -> k z (inj₂ (y₁              ,  cy₂′  ))  ) cy₂  y₂
  next (  C ▷ _    ) k (≡-refl , cy)      y   =  next   C   (\z cy′   -> k z (≡-refl , cy′)                      ) cy   y

  right : Nav
  right (x ,  []        )  =  ∅
  right (x ,  (c ∷ cs)  )  =  next FC (\z c′ -> z , (c′ ∷ cs)) c x 

  enter : {x : Ix} -> ⟨ x ⟩ -> Loc x
  enter x = x , []

  leave : {x : Ix} -> Loc x -> ⟨ x ⟩
  leave (x , [])        =  x
  leave (x , (c ∷ cs))  =  leave (to (fill FC c x) , cs)

  update : ((x : Ix) -> ⟨ x ⟩ -> ⟨ x ⟩) -> Nav
  update f (x , cs) = return (f _ x , cs)

  on :  {A : Set} -> ((x : Ix) -> ⟨ x ⟩ -> A) ->
        {x : Ix} -> Loc x -> A
  on f (x , cs) = f _ x

module ZipperExample where

  open AST
  open Zipper AST
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
      where  simp : (n : Ix) -> ⟨ n ⟩ -> ⟨ n ⟩
             simp n x with viewAST n
             simp (. _) e  |  vexpr  =  econst (eval e empty)
             simp (. _) d  |  vdecl  =  d
             simp (. _) v  |  vvar   =  v

  target = elet ("x" ≔ econst 54) (eadd (evar "x") (evar "y"))
  testZipper : callZipper ≡ just target
  testZipper = ≡-refl

module ListExample where

  open List
  open Base 2

  listmap' : {A B C : Set} {y : Ix} -> ({x : Ix} -> ListI A x -> ListI B x) -> ⟦ ListC ⟧ (ListI A) y -> ⟦ ListC ⟧ (ListI B) y
  listmap' {A} {B} {C} f xs = map ListC (\ {x} -> f {x}) xs

  -- does not termination-check:
  listmap : {A B : Set} -> (A -> B) -> List A -> List B
  listmap {A} {B} f xs = toList (listmap' {A} {B} {⊤} (\ {x} -> f' x) (fromList {zero} xs))
    where f' : (x : Ix) -> ListI A x -> ListI B x
          f' zero       xs = listmap f xs
          f' (suc zero) a  = f a
          f' (suc (suc ())) _

  testlistmap : listmap (\ n -> n + 1) (0 ∷ 1 ∷ 2 ∷ []) ≡ (1 ∷ 2 ∷ 3 ∷ [])
  testlistmap = ≡-refl