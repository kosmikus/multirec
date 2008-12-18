module Simple where

open import Data.Fin using (Fin; suc; zero)
open import Data.Nat using (ℕ; suc; zero; _≟_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_; _,_)
open import Data.Unit using (⊤)
open import Data.Bool using (Bool; true; false)

module Base (n : ℕ) where

  Ix = Fin n

  data Code : Set1 where
    I   : Code
    E   : Ix -> Code
    K   : Set -> Code
    _⊕_ : Code -> Code -> Code
    _⊛_ : Code -> Code -> Code

  infixr 6 _⊛_
  infixr 4 _⊕_

  ⟦_⟧ : Code -> (Ix -> Set) -> Set -> Set
  ⟦ I ⟧     _    A = A
  ⟦ E n ⟧   elem _ = elem n
  ⟦ K X ⟧   _    _ = X
  ⟦ F ⊕ G ⟧ elem A = ⟦ F ⟧ elem A ⊎ ⟦ G ⟧ elem A
  ⟦ F ⊛ G ⟧ elem A = ⟦ F ⟧ elem A × ⟦ G ⟧ elem A

  record Rep : Set1 where
    field
      FC    : Code
      Type  : (Ix -> Set) -> Set
      from  : {elems : Ix -> Set} -> (Type elems) -> ⟦ FC ⟧ elems (Type elems)
      to    : {elems : Ix -> Set} -> ⟦ FC ⟧ elems (Type elems) -> (Type elems)

  elems₂ : Set -> Set -> Fin 2 -> Set
  elems₂ A B zero       = A
  elems₂ A B (suc zero) = B
  elems₂ _ _ (suc (suc ()))

module List where
  
  open import Data.List
  open import Data.Function

  open Base 1

  ListF : Code
  ListF = K ⊤ ⊕ E zero ⊛ I

  fromList : {A : Set} -> List A -> ⟦ ListF ⟧ (const₁ A) (List A)
  fromList []       = inj₁ _
  fromList (x ∷ xs) = inj₂ (x , xs)

  toList : {A : Set} -> ⟦ ListF ⟧ (const₁ A) (List A) -> List A
  toList (inj₁ _)        = []
  toList (inj₂ (x , xs)) = x ∷ xs

  ListRep : Rep
  ListRep = record 
    { FC   = ListF
    ; Type = \f -> List (f zero)
    ; from = fromList
    ; to   = toList
    }

module Tree where
  
  open Base 2
  
  data Tree (A B : Set) : Set where
    empty  : Tree A B
    leaf   : A -> Tree A B
    branch : Tree A B -> B -> Tree A B -> Tree A B

  TreeF : Code
  TreeF = K ⊤ ⊕ E zero ⊕ I ⊛ E (suc zero) ⊛ I

  fromTree : {A B : Set} -> Tree A B -> ⟦ TreeF ⟧ (elems₂ A B) (Tree A B)
  fromTree empty          = inj₁ _
  fromTree (leaf x)       = inj₂ (inj₁ x)
  fromTree (branch l y r) = inj₂ (inj₂ (l , y , r))

  toTree : {A B : Set} -> ⟦ TreeF ⟧ (elems₂ A B) (Tree A B) -> Tree A B
  toTree (inj₁ _)                  = empty
  toTree (inj₂ (inj₁ x))           = leaf x
  toTree (inj₂ (inj₂ (l , y , r))) = branch l y r

  TreeRep : Rep
  TreeRep = record
    { FC   = TreeF
    ; Type = \f -> Tree (f zero) (f (suc zero))
    ; from = fromTree
    ; to   = toTree
    }

module Map {n : ℕ} (R : Base.Rep n) where

  open Base n public
  open Rep R

  mutual
    map' : (C : Code) -> {elems₁ elems₂ : Ix -> Set} -> ((ix : Ix) -> elems₁ ix -> elems₂ ix) -> ⟦ C ⟧ elems₁ (Type elems₁) -> ⟦ C ⟧ elems₂ (Type elems₂)
    map' I {elems₁} {elems₂} f i        = map elems₁ elems₂ f i -- to {elems₂} (map' FC {elems₁} {elems₂} f (from {elems₁} i))
    map' (E n)               f x        = f n x
    map' (K A)               _ x        = x
    map' (F ⊕ G)             f (inj₁ x) = inj₁ (map' F f x)
    map' (F ⊕ G)             f (inj₂ x) = inj₂ (map' G f x)
    map' (F ⊛ G)             f (x , y)  = map' F f x , map' G f y

    map : (elems₁ elems₂ : Ix -> Set) -> ((ix : Ix) -> elems₁ ix -> elems₂ ix) -> Type elems₁ -> Type elems₂
    map elems₁ elems₂ f x = to {elems₂} (map' FC {elems₁} {elems₂} f (from {elems₁} x))

-- for testing

isEven : ℕ -> Bool
isEven 0             = true
isEven 1             = false
isEven (suc (suc n)) = isEven n

module MapListTest where
  open List
  open Map ListRep
  open Rep ListRep
  open import Data.List hiding (map)
  open import Data.Function
  open import Relation.Binary.PropositionalEquality

  test : map (const₁ ℕ) (const₁ Bool) (const isEven) (1 ∷ 2 ∷ 3 ∷ []) ≡ false ∷ true ∷ false ∷ []
  test = ≡-refl

module MapTreeTest where
  open Tree
  open Map TreeRep
  open Rep TreeRep
  open import Data.Nat.Show
  open import Data.String
  open import Relation.Binary.PropositionalEquality

  f : (ix : Ix) -> elems₂ ℕ ℕ ix -> elems₂ Bool String ix
  f zero         = isEven
  f (suc (zero)) = show
  f (suc (suc ()))

  tree₁ = branch (leaf 1) 3 (branch (leaf 2) 4 empty)
  tree₂ = branch (leaf false) "3" (branch (leaf true) "4" empty)

  test : map (elems₂ ℕ ℕ) (elems₂ Bool String) f tree₁ ≡ tree₂
  test = ≡-refl