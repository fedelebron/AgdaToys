open import Relation.Binary
open import Level hiding (zero)
module SortedVector (T : TotalOrder Level.zero Level.zero Level.zero) where

open TotalOrder T
open import MyNat renaming (_≤_ to _≤ℕ_)
open import Data.Sum

data SortedVector : ℕ → Set
data _≤*_ : {n : ℕ} → Carrier → SortedVector n → Set

data SortedVector where
  ε : SortedVector zero
  _►_[_] : {n : ℕ} → (x : Carrier) (v : SortedVector n) → (x ≤* v) → SortedVector (succ n)

data _≤*_ where
  ≤*-base : (x : Carrier) → x ≤* ε
  ≤*-ind : {n : ℕ} {y : Carrier} {ys : SortedVector n} {p : y ≤* ys} → (x : Carrier) → (x ≤ y) → x ≤* (y ► ys [ p ])

data _≡_+_ : {n : ℕ} → SortedVector (succ n) → SortedVector n → Carrier → Set where
  ≡+-base : {n : ℕ} {x : Carrier} {v : SortedVector n} {p : x ≤* v} → (x ► v [ p ]) ≡ v + x
  ≡+-ind : {n : ℕ} {y : Carrier} {v : SortedVector n} {p : y ≤* v} {xv : SortedVector (succ n)} → (x : Carrier) → (y≤*xv : y ≤* xv) → (q : xv ≡ v + x) → ((y ► xv [ y≤*xv ]) ≡ (y ► v [ p ]) + x) 

lemma-≤*≡+ : {n : ℕ} → (v : SortedVector n) → (xv : SortedVector (succ n)) → (x y : Carrier) → (y≤x : y ≤ x) → (y≤*v : y ≤* v) (p : xv ≡ v + x) → y ≤* xv
lemma-≤*≡+ ε ._ x y y≤x y≤*v ≡+-base = ≤*-ind y y≤x
lemma-≤*≡+ (t ► v [ q ]) ._ x y y≤x (≤*-ind .y x′) ≡+-base = ≤*-ind y y≤x
lemma-≤*≡+ (_ ► _ [ _ ]) ._ x y y≤x (≤*-ind .y x′) (≡+-ind .x y≤*vxs p) = ≤*-ind y x′       

record Certificate (x : Carrier) {n : ℕ} (v : SortedVector n) : Set where
  field
    w : SortedVector (succ n)
    proof : w ≡ v + x
    
insert : {n : ℕ} → (x : Carrier) → (v : SortedVector n) → Certificate x v
insert x ε = record { w = x ► ε [ ≤*-base x ] ; proof = ≡+-base }
insert x (y ► v [ p ]) with total x y
...                    | inj₁ x≤y = record { w = x ► y ► v [ p ] [ ≤*-ind x x≤y ] ; proof = ≡+-base }
...                    | inj₂ y≤x = let R  = insert x v
                                        xv = Certificate.w R
                                        q = Certificate.proof R
                                        p′ = lemma-≤*≡+ v xv x y y≤x p q
                                    in record { w = y ► xv [ p′ ]
                                              ; proof = ≡+-ind x p′ q
                                              }
