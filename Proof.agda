module Proof where

open import Agda.Primitive
open import Reflection
open import Data.Fin
open import Data.Fin.Properties using (eq? ; _≟_)
open import Data.Nat hiding (eq? ;  _+_ ; suc ; zero) 
open import Data.List
open import Data.String hiding (setoid)
open import Data.Product using (_,_ ; _×_)
open import Data.Bool
open import Relation.Binary
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl ; cong ; setoid)
import Relation.Binary.Indexed as I
open import Function using (_∘_ ; _$_ ; _∋_)
open import Function.Equality using (_⟶_ ;  _⟨$⟩_ )
open import Function.Injection using (_↣_ ; Injective ; Injection)
open import Relation.Nullary
open import Relation.Nullary.Negation

data Test : Set where
  A : Bool -> Test
  B : Fin 2 -> Test

convert : Test -> Fin 4
convert (A true) = zero
convert (A false) = suc (zero)
convert (B x) = (fromℕ 2) + x

lemma : {x x₁ : Bool} -> convert (A x) ≡ convert (A x₁) -> x ≡ x₁
lemma {true} {true} p = refl
lemma {true} {false} ()
lemma {false} {true} ()
lemma {false} {false} p = refl

lemma₁ : {n : ℕ} {x x₁ : Fin n} -> suc (suc x) ≡ suc (suc x₁) -> x ≡ x₁
lemma₁ {ℕ.zero} refl = refl
lemma₁ {ℕ.suc n} refl = refl

mehinj : Test ↣ Fin 4
mehinj = record { to = preserves-eq ; injective = injective` }
  where
    cong` : Setoid._≈_ (setoid Test) I.=[ convert ]⇒ Setoid._≈_ (setoid (Fin 4))
    cong` {A x} {A .x} refl = refl
    cong` {A x} {B y} ()
    cong` {B x} {A y} ()
    cong` {B x} {B .x} refl = refl

    preserves-eq : setoid Test ⟶ setoid (Fin 4)
    preserves-eq = record { _⟨$⟩_ = convert ; cong = cong` }
    
    injective` : Injective preserves-eq
    injective` {A x} {A x₁} p with (Data.Bool._≟_ x x₁)
    injective` {A x} {A .x} p | yes refl = refl
    injective` {A x} {A x₁} p | no ¬p2 = contradiction (lemma p) ¬p2
    injective` {A x} {B y} ()
    injective` {B x} {A y} ()
    injective` {B x} {B x₁} p with (Data.Fin.Properties._≟_ x x₁)
    injective` {B x} {B .x} p₁ | yes refl = refl
    injective` {B x} {B x₁} p | no ¬p2 = contradiction (lemma₁ p) ¬p2    
