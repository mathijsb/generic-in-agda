module Serializer.Vec where

open import Data.Fin hiding (_+_)
open import Data.Nat
open import Data.Vec
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

open Serializer.Serializer

-----------------------------------
-- Generic instance for Vec
-----------------------------------

2^ : ℕ -> ℕ
2^ zero = 1
2^ (suc b) = 2 * 2^ b

-- inverted exponent
_^_ : ℕ -> ℕ -> ℕ
zero ^ a = 1
suc b ^ a = a * (b ^ a)

fromVec : ∀ {n} {A : Set} -> {{t : Serializer A}} -> Vec A n -> Fin (n ^ (size {A}))
fromVec {zero} [] = zero
fromVec {suc n} {a} (x ∷ v) = × (size {a}) (n ^ (size {a})) (from x) (fromVec v)

toVec` : ∀ {n} {A : Set} -> {{t : Serializer A}} -> Fin (n ^ (size {A})) -> Vec A n
toVec` {zero} x = []
toVec` {suc n} {a} {{t}} x with Serializer.to t | toVec` {n} {a} {{t}}
... | to1 | to2 with Serializer.size t
... | s with ⨂ s (n ^ s) x
toVec` {suc n} .(× s (n ^ s) i j) | to1 | to2 | s | is× i j = to1 i ∷ to2 j

vec-from-cong : ∀ {n} {A : Set} -> {{t : Serializer A}} -> Setoid._≈_ (setoid (Vec A n)) I.=[ fromVec ]⇒ Setoid._≈_ (setoid (Fin (n ^ (size {A}))))
vec-from-cong refl = refl

vec-from-preserves-eq : ∀ {n} {A : Set} -> {{t : Serializer A}} -> setoid (Vec A n) ⟶ setoid (Fin (n ^ (size {A})))
vec-from-preserves-eq = record { _⟨$⟩_ = fromVec ; cong = vec-from-cong }

vec-from-injective : ∀ {n} {A : Set} -> {{t : Serializer A}} -> Injective (vec-from-preserves-eq {n} {A} {{t}})
vec-from-injective {zero} {a} {{t}} {x = []} {[]} x₁ with fromVec {A = a} {{t}} []
... | p1 = refl
vec-from-injective {suc n} {a} {{t}} {x ∷ x₁} {y ∷ y₁} p  with (⨂ (Serializer.size t) (n ^ (Serializer.size t)) (fromVec (x ∷ x₁))) | (⨂ (Serializer.size t) (n ^ (Serializer.size t)) (fromVec (y ∷ y₁)))
... | a1 | b2 with vec-from-injective {n} {_} {{t}} {x₁} {y₁}
... | c with c (×-equal₁ {x₁ = (Serializer.from t x)} {x₂ = (Serializer.from t y)} p) | (×-equal₂ {x₁ = (Serializer.from t x)} {x₂ = (Serializer.from t y)} p)
... | p1 | p2 with Serializer.from t
... | la = ? 

--(Injection.injective (Serializer.injection t))

{-
vec-from-injective : ∀ {n} -> Injective (vec-from-preserves-eq {n})
vec-from-injective {zero} {[]} {[]} p with fromVec []
... | p2 = refl
vec-from-injective {suc n} {x ∷ x₁} {y ∷ y₁} p with (⨂ 2 (2^ n) (fromVec (x ∷ x₁))) | (⨂ 2 (2^ n) (fromVec (y ∷ y₁)))
... | a1 | b2 with vec-from-injective {n} {x₁} {y₁}
... | c with c (×-equal₁ {x₁ = (fromBool x)} {x₂ = (fromBool y)} p) | (×-equal₂ {x₁ = (fromBool x)} {x₂ = (fromBool y)} p)
... | p1 | p2 with from-bool-injective p2 
vec-from-injective {suc n} {x ∷ x₁} {.x ∷ .x₁} p | a1 | b2 | c | refl | p2 | refl = refl

-}


vec-from-surjective : ∀ {n} {A : Set} -> {{t : Serializer A}} -> Surjective (vec-from-preserves-eq {n} {A} {{t}})
vec-from-surjective {n} {a} {{t}} = record { from = preserves-eq-inv ; right-inverse-of = (inv {n} {a} {{t}}) }
  where
    cong-inverse : ∀ {n} {A : Set} -> {{t : Serializer A}} -> Setoid._≈_ (setoid (Fin (n ^ (size {A})))) I.=[ toVec` ]⇒ Setoid._≈_ (setoid (Vec A n))
    cong-inverse refl = refl
    
    preserves-eq-inv : ∀ {n} {A : Set} -> {{t : Serializer A}} -> setoid (Fin (n ^ (size {A}))) ⟶ setoid (Vec A n)
    preserves-eq-inv = record { _⟨$⟩_ = toVec` ; cong = cong-inverse }
    
    inv : ∀ {n} {A : Set} -> {{t : Serializer A}} -> (preserves-eq-inv {n} {A} {{t}}) RightInverseOf (vec-from-preserves-eq {n} {A} {{t}})
    inv {zero} zero = refl
    inv {zero} (suc ())
    inv {suc n₁} {a} {{t}} x with ⨂ (Serializer.size t) (n₁ ^ (Serializer.size t)) x
    inv {suc n₁} {a} {{t}} ._ | is× i j with (Surjective.right-inverse-of (Bijective.surjective (Bijection.bijective (Serializer.bijection t)))) i
    ... | ple = {!!} 
--      rewrite  (inv {n₁} {a} {{t}} j)
--      ... | ple = ?
      
--    ... | moo with (inv {n₁} {a} {{t}} j)
--    ... | moo1 = refl --  {!!}
{-
    inv {suc n₁} ._ | is× i j with  (Surjective.right-inverse-of (Bijective.surjective (Bijection.bijective (Serializer.bijection t))))
    ... | moo = {!!}-}
    
--      rewrite (Surjective.right-inverse-of (Bijective.surjective (Bijection.bijective (Serializer.bijection t)))) i | (inv {n₁} j) = refl
    
{-
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
-}
