module MyNat where

open import Function using (_∘_)
import Level
open import Data.Sum using (_⊎_) renaming (map to map′)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning using (_≡⟨_⟩_; begin_; _∎)

data ℕ : Set where
  zero : ℕ
  succ : ℕ → ℕ

{-# BUILTIN NATURAL ℕ #-}

_+_ : ℕ → ℕ → ℕ
zero + n = n
(succ n) + m = succ (n + m)
infixl 6 _+_

leftId : (n : ℕ) → zero + n ≡ n
leftId n = refl

rightId : (n : ℕ) → n + zero ≡ n
rightId zero = refl
rightId (succ n) =
  begin
    (succ n) + zero    ≡⟨ refl ⟩
    succ (n + zero)    ≡⟨ cong succ (rightId n) ⟩
    succ n
  ∎

+-commutativity : (n m : ℕ) → n + m ≡ m + n
+-commutativity zero m = sym (rightId m)
+-commutativity (succ n) zero = cong succ (rightId n)
+-commutativity (succ n) (succ m) =
  begin
    (succ n) + (succ m)      ≡⟨ refl ⟩
    succ (n + succ m)        ≡⟨ cong succ (+-commutativity n (succ m))⟩
    succ (succ m + n)        ≡⟨ cong succ refl ⟩
    succ (succ (m + n))      ≡⟨ cong (succ ∘ succ) (+-commutativity  m n)⟩
    succ (succ (n + m))      ≡⟨ cong succ refl ⟩
    succ (succ n + m)        ≡⟨ cong succ (+-commutativity (succ n) m) ⟩
    succ (m + succ n)        ≡⟨ refl ⟩
    succ m + succ n
  ∎    

+-associativity : (n m p : ℕ) → n + (m + p) ≡ (n + m) + p
+-associativity zero m p = refl
+-associativity (succ n) zero p = cong succ (+-associativity n zero p)
+-associativity (succ n) (succ m) zero = cong succ (+-associativity n (succ m) zero)
+-associativity (succ n) (succ m) (succ p) = cong succ (+-associativity n (succ m) (succ p))


_*_ : ℕ → ℕ → ℕ
zero * n = zero
(succ n) * m = m + n * m
infixl 7 _*_

rightAbsorb : (n : ℕ) → n * zero ≡ zero
rightAbsorb zero = refl
rightAbsorb (succ n) = rightAbsorb n

*-commutativity : (n m : ℕ) → n * m ≡ m * n
*-commutativity zero m = sym (rightAbsorb m)
*-commutativity (succ n) zero = *-commutativity n zero
*-commutativity (succ n) (succ m) =    
   begin
    (succ n) * (succ m)     ≡⟨ refl ⟩
    succ m + (n * succ m)   ≡⟨ cong (λ x → succ m + x) (*-commutativity n (succ m)) ⟩
    succ m + (succ m * n)   ≡⟨ refl ⟩
    succ (m + (n + m * n))  ≡⟨ cong succ (+-associativity m n (m * n)) ⟩
    succ ((m + n) + m * n)  ≡⟨ cong (λ x → succ (x + m * n)) (+-commutativity m n) ⟩
    succ ((n + m) + m * n)  ≡⟨ cong succ (sym (+-associativity n m (m * n))) ⟩
    succ (n + (m + m * n))  ≡⟨ cong (λ x → succ (n + (m + x))) (*-commutativity m n) ⟩
    succ (n + (m + n * m))  ≡⟨ refl ⟩
    succ n + (succ n * m)   ≡⟨ cong (λ x → succ n + x) (*-commutativity (succ n) m) ⟩
    succ n + (m * succ n)   ≡⟨ refl ⟩
    succ m * succ n
  ∎

*-associativity : (n m p : ℕ) → n + (m + p) ≡ (n + m) + p
*-associativity zero m p = refl
*-associativity (succ n) zero p = cong succ (*-associativity n zero p)
*-associativity (succ n) (succ m) zero = cong succ (*-associativity n (succ m) zero)
*-associativity (succ n) (succ m) (succ p) = cong succ (*-associativity n (succ m) (succ p))



+*-distributivity : (n m p : ℕ) → n * (m + p) ≡ n * m + n * p
+*-distributivity zero m p = refl
+*-distributivity (succ n) zero p =
  begin
    p + n * p              ≡⟨ refl ⟩
    zero + (p + n * p)     ≡⟨ cong (λ x → x + (p + n * p)) (sym (rightAbsorb n)) ⟩
    n * zero + (p + n * p)
  ∎
+*-distributivity (succ n) (succ m) zero =
  begin
    succ n * (succ m + zero)  ≡⟨ cong (λ x → succ n * x) (rightId (succ m)) ⟩
    succ n * succ m           ≡⟨ sym (rightId (succ n * succ m)) ⟩
    succ n * succ m + zero    ≡⟨ cong (λ x → succ n * succ m + x) (sym (rightAbsorb (succ n))) ⟩
    succ n * succ m + succ n * zero
  ∎

+*-distributivity (succ n) (succ m) (succ p) =
  begin
    succ n * (succ m + succ p)                     ≡⟨ refl ⟩
    succ m + succ p + n * (succ m + succ p)        ≡⟨ cong (λ x → (succ m + succ p + x)) (+*-distributivity n (succ m) (succ p)) ⟩
    (succ m + succ p) + (n * succ m + n * succ p)  ≡⟨ sym (+-associativity (succ m) (succ p) (n * succ m + n * succ p)) ⟩
    succ m + (succ p + (n * succ m + n * succ p))  ≡⟨ cong (λ x → succ m + x) (+-associativity (succ p) (n * succ m) (n * succ p)) ⟩
    succ m + ((succ p + n * succ m) + n * succ p)  ≡⟨ cong (λ x → succ m + (x + n * succ p)) (+-commutativity (succ p) (n * succ m)) ⟩
    succ m + ((n * succ m + succ p) + n * succ p) ≡⟨ cong (λ x → succ m + x) (sym (+-associativity (n * succ m) (succ p) (n * succ p))) ⟩
    succ m + (n * succ m + (succ p + n * succ p))  ≡⟨ +-associativity (succ m) (n * succ m) (succ p + n * succ p) ⟩
    (succ m + n * succ m) + (succ p + n * succ p)  ≡⟨  refl ⟩
    (succ n) * (succ m) + (succ n) * (succ p)
  ∎

data _≤_ : Rel ℕ Level.zero where
  ≤-base : (n : ℕ) → zero ≤ n
  ≤-ind  : (n m : ℕ) → n ≤ m → succ n ≤ succ m
infix 4 _≤_


≤-refl : Reflexive _≤_
≤-refl {zero} = ≤-base zero
≤-refl {succ n} = ≤-ind n n ≤-refl

≤-transitivity : Transitive _≤_
≤-transitivity {zero} {j} {k} p q = ≤-base k
≤-transitivity {succ i} {zero} () _
≤-transitivity {succ i} {succ j} {zero} _ ()
≤-transitivity {succ .i} {succ .j} {succ .k} (≤-ind i j p) (≤-ind .j k q) = ≤-ind i k (≤-transitivity p q)

≤-antisymmetry : Antisymmetric _≡_ _≤_ -- (n m : ℕ) → n ≤ m → m ≤ n → n ≡ m
≤-antisymmetry {zero} {zero} p q = refl
≤-antisymmetry {zero} {succ m} p ()
≤-antisymmetry {succ n} {zero} () q
≤-antisymmetry {succ n} {succ m} (≤-ind .n .m p) (≤-ind .m .n q) = sym (cong succ (≤-antisymmetry q p))

≤-monotonicity : succ Preserves _≤_ ⟶ _≤_
≤-monotonicity {i} {j} p = ≤-ind i j p

≤-totality : Total {Level.zero} {Level.zero} {ℕ} _≤_
≤-totality zero y = _⊎_.inj₁ (≤-base y)
≤-totality p zero = _⊎_.inj₂ (≤-base p)
≤-totality (succ p) (succ y) = map′ ≤-monotonicity ≤-monotonicity (≤-totality p y)

totalOrder : TotalOrder _ _ _
totalOrder = record
  { Carrier  = ℕ
  ; _≈_      = _≡_
  ; _≤_      = _≤_
  ; isTotalOrder = record
      { isPartialOrder = record
          { isPreorder = record
              { isEquivalence    = isEquivalence
              ; reflexive        = refl′
              ; trans            = ≤-transitivity
              }
            ; antisym = ≤-antisymmetry
          }
       ; total = ≤-totality
       }
 }
   where
     refl′ : _≡_ ⇒ _≤_
     refl′ refl = ≤-refl
