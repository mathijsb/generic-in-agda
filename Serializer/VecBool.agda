module Serializer.VecBool where

open import Data.Fin hiding (_+_)
open import Data.Nat
open import Data.Vec
open import Data.Bool
open import Function using (_∘_ ; _$_ ; _∋_ ; id ; const)
open import Function.Bijection
open import Function.Injection
open import Function.Surjection
open import Function.Equality using (_⟶_ ;  _⟨$⟩_ ; Π )
open import Function.LeftInverse hiding (_∘_)
open import Relation.Binary
open import Relation.Binary.EqReasoning
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl ; cong ; setoid )
import Relation.Binary.Indexed as I

open import Serializer
open import Helper.Fin
open import Serializer.Bool

open Serializer.Serializer {{...}}

2^ : ℕ -> ℕ
2^ zero = 1
2^ (suc b) = 2 * 2^ b

--fromVec : ∀ {a n} {A : Set a} -> Vec A n -> Fin n
fromVec : ∀ {n} -> Vec Bool n -> Fin (2^ n)
fromVec {zero} [] = zero
fromVec {suc n} (x ∷ x₁) = × 2 (2^ n) (from x) (fromVec x₁)

toVec` : ∀ {n} -> Fin (2^ n) -> Vec Bool n
toVec` {zero} x = []
toVec` {suc n} x with ⨂ 2 (2^ n) x
toVec` {suc n} .(× 2 (2^ n) i j) | is× i j = (to i) ∷ (toVec` j)

vec-from-cong : ∀ {n} -> Setoid._≈_ (setoid (Vec Bool n)) I.=[ fromVec ]⇒ Setoid._≈_ (setoid (Fin (2^ n)))
vec-from-cong refl = refl

vec-from-preserves-eq : ∀ {n} -> setoid (Vec Bool n) ⟶ setoid (Fin (2^ n))
vec-from-preserves-eq = record { _⟨$⟩_ = fromVec ; cong = vec-from-cong }

vec-from-injective : ∀ {n} -> Injective (vec-from-preserves-eq {n})
vec-from-injective {zero} {[]} {[]} p with fromVec []
... | p2 = refl
vec-from-injective {suc n} {x ∷ x₁} {y ∷ y₁} p with (⨂ 2 (2^ n) (fromVec (x ∷ x₁))) | (⨂ 2 (2^ n) (fromVec (y ∷ y₁)))
... | a1 | b2 with vec-from-injective {n} {x₁} {y₁}
... | c with c (×-equal₁ {x₁ = (fromBool x)} {x₂ = (fromBool y)} p) | (×-equal₂ {x₁ = (fromBool x)} {x₂ = (fromBool y)} p)
... | p1 | p2 with from-bool-injective p2 
vec-from-injective {suc n} {x ∷ x₁} {.x ∷ .x₁} p | a1 | b2 | c | refl | p2 | refl = refl

vec-from-surjective : ∀ {n} -> Surjective (vec-from-preserves-eq {n})
vec-from-surjective {n} = record { from = preserves-eq-inv ; right-inverse-of = (inv {n}) }
  where
    cong-inverse : ∀ {n} -> Setoid._≈_ (setoid (Fin (2^ n))) I.=[ toVec` ]⇒ Setoid._≈_ (setoid (Vec Bool n))
    cong-inverse refl = refl
    
    preserves-eq-inv : ∀ {n} -> setoid (Fin  (2^ n)) ⟶ setoid (Vec Bool n)
    preserves-eq-inv = record { _⟨$⟩_ = toVec` ; cong = cong-inverse }
    
    inv : ∀ {n} -> (preserves-eq-inv {n}) RightInverseOf (vec-from-preserves-eq {n})
    inv {zero} zero = refl
    inv {zero} (suc ())
    inv {suc n₁} x with ⨂ 2 (2^ n₁) x
    inv {suc n₁} .(× 2 (2^ n₁) i j) | is× i j
      rewrite (Surjective.right-inverse-of (Bijective.surjective (Bijection.bijective (bijection {Bool})))) i | (inv {n₁} j) = refl
