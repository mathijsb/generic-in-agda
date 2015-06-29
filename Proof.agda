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
open import Function.LeftInverse
open import Function.Injection using (_↣_ ; Injective ; Injection)
open import Function.Surjection using (_↠_ ; Surjective ; Surjection)
open import Function.Bijection using (Bijection)
open import Relation.Nullary
open import Relation.Nullary.Negation

data Test : Set where
  A : Bool -> Test
  B : Fin 2 -> Test

from : Test -> Fin 4
from (A true) = zero
from (A false) = suc (zero)
from (B x) = (fromℕ 2) + x

to : Fin 4 -> Test
to zero = A true
to (suc zero) = A false
to (suc (suc zero)) = B zero
to (suc (suc (suc x))) = B (suc zero)

lemma : {x x₁ : Bool} -> from (A x) ≡ from (A x₁) -> x ≡ x₁
lemma {true} {true} p = refl
lemma {true} {false} ()
lemma {false} {true} ()
lemma {false} {false} p = refl

lemma₁ : {n : ℕ} {x x₁ : Fin n} -> suc (suc x) ≡ suc (suc x₁) -> x ≡ x₁
lemma₁ {ℕ.zero} refl = refl
lemma₁ {ℕ.suc n} refl = refl

from-cong : Setoid._≈_ (setoid Test) I.=[ from ]⇒ Setoid._≈_ (setoid (Fin 4))
from-cong {A x} {A .x} refl = refl
from-cong {A x} {B y} ()
from-cong {B x} {A y} ()
from-cong {B x} {B .x} refl = refl

from-preserves-eq : setoid Test ⟶ setoid (Fin 4)
from-preserves-eq = record { _⟨$⟩_ = from ; cong = from-cong }

from-injective : Injective from-preserves-eq
from-injective {A x} {A x₁} p with (Data.Bool._≟_ x x₁)
from-injective {A x} {A .x} p | yes refl = refl
from-injective {A x} {A x₁} p | no ¬p2 = contradiction (lemma p) ¬p2
from-injective {A x} {B y} ()
from-injective {B x} {A y} ()
from-injective {B x} {B x₁} p with (Data.Fin.Properties._≟_ x x₁)
from-injective {B x} {B .x} p₁ | yes refl = refl
from-injective {B x} {B x₁} p | no ¬p2 = contradiction (lemma₁ p) ¬p2

from-surjective : Surjective from-preserves-eq
from-surjective = record { from = preserves-eq-inv ; right-inverse-of = inv }
  where
    cong-inverse : Setoid._≈_ (setoid (Fin 4)) I.=[ to ]⇒ Setoid._≈_ (setoid Test)
    cong-inverse {zero} refl = refl
    cong-inverse {suc zero} refl = refl
    cong-inverse {suc (suc zero)} refl = refl
    cong-inverse {suc (suc (suc i))} refl = refl
    
    preserves-eq-inv : setoid (Fin 4) ⟶ setoid Test
    preserves-eq-inv = record { _⟨$⟩_ = to ; cong = cong-inverse }

    inv : preserves-eq-inv RightInverseOf from-preserves-eq
    inv zero = refl
    inv (suc zero) = refl
    inv (suc (suc zero)) = refl
    inv (suc (suc (suc zero))) = refl
    inv (suc (suc (suc (suc ()))))

from-injection : Test ↣ Fin 4
from-injection = record { to = from-preserves-eq ; injective = from-injective }

from-surjection : Test ↠ Fin 4
from-surjection = record { to = from-preserves-eq ; surjective = from-surjective }

from-bijection : Bijection (setoid Test) (setoid (Fin 4))
from-bijection = record { to = from-preserves-eq ; bijective = record { injective = from-injective ; surjective = from-surjective } }
