module Helper.Fin where

open import Data.Fin hiding (_+_)
open import Data.Nat
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Relation.Nullary.Negation

------------------------------------------------------------------------
-- Fin magic
------------------------------------------------------------------------

+₁ : (x y : ℕ) (i : Fin x) -> Fin (x + y)
+₁ zero    y ()
+₁ (suc x) y zero = zero
+₁ (suc x) y (suc i) = suc (+₁ x y i)
  
+₂ : (x y : ℕ) (j : Fin y) -> Fin (x + y)
+₂ zero    y j = j
+₂ (suc x) y j = suc (+₂ x y j)

data Fin+ (x y : ℕ) : Fin (x + y) -> Set where
  is+₁ : (i : Fin x) -> Fin+ x y (+₁ x y i)
  is+₂ : (j : Fin y) -> Fin+ x y (+₂ x y j)

⨁ : (x y : ℕ) (i : Fin (x + y)) -> Fin+ x y i
⨁ zero y i = is+₂ i
⨁ (suc x) y zero = is+₁ zero
⨁ (suc x) y (suc i) with ⨁ x y i
⨁ (suc x) y (suc ._) | is+₁ i = is+₁ (suc i)
⨁ (suc x) y (suc ._) | is+₂ j = is+₂ j

[_,_] : {X : Set} {x y : ℕ} (l : Fin x -> X) (r : Fin y -> X) -> (s : Fin (x + y)) -> X
[_,_] {X} {x} {y} l r s with ⨁ x y s 
[_,_] l r ._ | is+₁ i = l i
[_,_] l r ._ | is+₂ j = r j

× : (x y : ℕ) (i : Fin x) (j : Fin y) -> Fin (x * y)
× zero _ () _ 
× (suc x) y zero j = +₁ y (x * y) j
× (suc x) y (suc i) j = +₂ y (x * y) (× x y i j)

data Fin* (x y : ℕ) : Fin (x * y) -> Set where
  is× : (i : Fin x) (j : Fin y) -> Fin* x y (× x y i j)

⨂ : (x y : ℕ) (i : Fin (x * y)) -> Fin* x y i
⨂ zero y ()
⨂ (suc x) y i with ⨁ y (x * y) i
⨂ (suc x) y ._ | is+₁ i = is× zero i
⨂ (suc x) y ._ | is+₂ j with ⨂ x y j
⨂ (suc x) y ._ | is+₂ ._ | is× i j  = is× (suc i) j

------------------------------------------------------------------------
-- Fin lemma's
------------------------------------------------------------------------

suc-eq : {n : ℕ} {x x₁ : Fin n} -> ((Data.Fin.suc x) ≡ (Data.Fin.suc x₁)) -> (x ≡ x₁)
suc-eq refl = refl

+-eq : {n n₁ : ℕ} {x x₁ : Fin n} -> (m : Fin n₁) -> ((m Data.Fin.+ x) ≡ (m Data.Fin.+ x₁)) -> (x ≡ x₁)
+-eq zero p = p
+-eq (suc m) p = +-eq m (suc-eq p)

+-eq₁ : {n n₁ : ℕ} {x x₁ : Fin n} -> (+₁ n n₁ x ≡ +₁ n n₁ x₁) -> (x ≡ x₁)
+-eq₁ {x = zero} {x₁ = zero} p = refl
+-eq₁ {x = zero} {suc x₁} ()
+-eq₁ {x = suc x} {zero} ()
+-eq₁ {x = suc x} {x₁ = suc x₁} p with +-eq (fromℕ 1) p
... | p1 with +-eq₁ p1
... | p2 = cong suc p2

+-eq₂ : {n n₁ : ℕ} {x x₁ : Fin n₁} -> (+₂ n n₁ x ≡ +₂ n n₁ x₁) -> (x ≡ x₁)
+-eq₂ {zero} refl = refl
+-eq₂ {suc n} {suc n₁} {zero} {zero} refl = refl
+-eq₂ {suc n} {suc n₁} {zero} {suc x₁} p with suc-eq p
... | p1 = +-eq₂ {n} {suc n₁} p1
+-eq₂ {suc n} {suc n₁} {suc x} {zero} p with suc-eq p
... | p1 = +-eq₂ {n} {suc n₁} p1
+-eq₂ {suc n} {suc n₁} {suc x} {suc x₁} p with suc-eq p
... | p1 = +-eq₂ {n} {suc n₁} p1

¬+-eq₁ : {n m : ℕ} {x : Fin n} {y : Fin m} -> ¬( (+₁ n m) x ≡ (+₂ n m) y)
¬+-eq₁ {zero} {zero} {()}
¬+-eq₁ {zero} {suc m} {()}
¬+-eq₁ {suc n} {zero} {y = ()}
¬+-eq₁ {suc n} {suc m} {zero} ()
¬+-eq₁ {suc n} {suc m} {suc x} {zero} with ¬+-eq₁ {n} {suc m} {x} {zero}
... | p1 = contraposition suc-eq p1
¬+-eq₁ {suc n} {suc m} {suc x} {suc y} with ¬+-eq₁ {n} {suc m} {x} {suc y}
... | p1 = contraposition suc-eq p1

¬+-eq₂ : {n m : ℕ} {x : Fin n} {y : Fin m} -> ¬( (+₂ n m) y ≡ (+₁ n m) x)
¬+-eq₂ {zero} {zero} {()} x₁
¬+-eq₂ {zero} {suc m} {()} x₁
¬+-eq₂ {suc n} {zero} {zero} ()
¬+-eq₂ {suc n} {zero} {suc x} {()}
¬+-eq₂ {suc n} {suc m} {zero} {zero} ()
¬+-eq₂ {suc n} {suc m} {zero} {suc y} ()
¬+-eq₂ {suc n} {suc m} {suc x} {zero} with ¬+-eq₂ {n} {suc m} {x} {zero}
... | p1 = contraposition suc-eq p1
¬+-eq₂ {suc n} {suc m} {suc x} {suc y} =  contraposition suc-eq (¬+-eq₂ {n} {suc m} {x} {suc y})

×-equal₁ : ∀ {n m : ℕ} {x₁ x₂ : Fin n} {y₁ y₂ : Fin m} -> (× n m x₁ y₁) ≡ (× n m x₂ y₂) -> (y₁ ≡ y₂)
×-equal₁ {zero} {x₁ = ()} x 
×-equal₁ {suc n} {zero} {y₁ = ()} x
×-equal₁ {suc n} {suc m} {zero} {zero} p = +-eq₁ p
×-equal₁ {suc n} {suc m} {zero} {suc x₂} {zero} ()
×-equal₁ {suc n} {suc m} {zero} {suc x₂} {suc y₁} p with suc-eq p
... | p1 with ¬+-eq₁ {m} {(n * suc m)} p1
×-equal₁ {suc n} {suc m} {zero} {suc x₂} {suc y₁} p | p1 | ()
×-equal₁ {suc n} {suc m} {suc x₁} {zero} {zero} {zero} p = refl
×-equal₁ {suc n} {suc m} {suc x₁} {zero} {zero} {suc y₂} p with suc-eq p
... | p1 with ¬+-eq₂ p1
×-equal₁ {suc n} {suc m} {suc x₁} {zero} {zero} {suc y₂} p | p1 | ()
×-equal₁ {suc n} {suc m} {suc x₁} {zero} {suc y₁} {zero} ()
×-equal₁ {suc n} {suc m} {suc x₁} {zero} {suc y₁} {suc y₂} p with suc-eq p
... | p1 with ¬+-eq₂ p1
×-equal₁ {suc n} {suc m} {suc x₁} {zero} {suc y₁} {suc y₂} p | p1 | ()
×-equal₁ {suc n} {suc m} {suc x₁} {suc x₂} p with suc-eq p
... | p2 with +-eq₂ {suc m} {(n * suc m)} p
... | p3 = ×-equal₁ {n} {suc m} p3

×-equal₂ : ∀ {n m : ℕ} {x₁ x₂ : Fin n} {y₁ y₂ : Fin m} -> (× n m x₁ y₁) ≡ (× n m x₂ y₂) -> (x₁ ≡ x₂)
×-equal₂ {zero} {x₁ = ()} x 
×-equal₂ {suc n} {zero} {y₁ = ()} x
×-equal₂ {suc n} {suc m} {zero} {zero} x = refl
×-equal₂ {suc n} {suc m} {zero} {suc x₂} {zero} {zero} ()
×-equal₂ {suc n} {suc m} {zero} {suc x₂} {zero} {suc y₂} ()
×-equal₂ {suc n} {suc m} {zero} {suc x₂} {suc y₁} {zero} p with suc-eq p
... | p1 with ¬+-eq₁ p1
×-equal₂ {suc n} {suc m} {zero} {suc x₂} {suc y₁} {zero} p | p1 | ()
×-equal₂ {suc n} {suc m} {zero} {suc x₂} {suc y₁} {suc y₂} p with suc-eq p
... | p1 with ¬+-eq₁ p1
×-equal₂ {suc n} {suc m} {zero} {suc x₂} {suc y₁} {suc y₂} p | p1 | ()
×-equal₂ {suc n} {suc m} {suc x₁} {zero} {y₂ = zero} ()
×-equal₂ {suc n} {suc m} {suc x₁} {zero} {zero} {suc y₂} p with suc-eq p
... | p1 with ¬+-eq₂ p1
×-equal₂ {suc n} {suc m} {suc x₁} {zero} {zero} {suc y₂} p | p1 | ()
×-equal₂ {suc n} {suc m} {suc x₁} {zero} {suc y₁} {suc y₂} p  with suc-eq p
... | p1 with ¬+-eq₂ p1
×-equal₂ {suc n} {suc m} {suc x₁} {zero} {suc y₁} {suc y₂} p | p1 | ()
×-equal₂ {suc n} {suc m} {suc x₁} {suc x₂} p with suc-eq p
... | p1 with +-eq₂ {m} {(n * suc m)} p1
... | p2 with ×-equal₂ {n} {suc m} p2
... | p3 = cong suc p3
