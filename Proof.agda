module Proof where

open import Agda.Primitive hiding (_⊔_)
open import Reflection
open import Data.Fin hiding (_+_)
open import Data.Fin.Properties using (eq? ; _≟_ )
open import Data.Nat hiding (eq? ; _⊔_)
open import Data.Nat.Properties
open import Data.List
open import Data.String hiding (setoid)
open import Data.Bool
open import Data.Vec
open import Relation.Binary
open import Relation.Binary.EqReasoning
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl ; cong ; setoid )
import Relation.Binary.Indexed as I
open import Function using (_∘_ ; _$_ ; _∋_ ; id ; const)
open import Function.Equality using (_⟶_ ;  _⟨$⟩_ ; Π )
open import Function.LeftInverse hiding (_∘_)
open import Function.Injection using (_↣_ ; Injective ; Injection )
open import Function.Surjection using (_↠_ ; Surjective ; Surjection)
open import Function.Bijection using (Bijection ; Bijective ; id )
open import Relation.Nullary
open import Relation.Nullary.Negation

open import Helper.Fin
open import Serializer
open import Serializer.Fin
open import Serializer.Bool

data Test : Set where
  A : Bool -> Test
  B : Fin 2 -> Bool -> Test
  C : Fin 2 -> Test

open Serializer.Serializer {{...}}

fromTest : Test -> Fin 8
fromTest (A x) = +₁ 6 2 (+₁ 2 4 (from x))
fromTest (B x x₁) = +₁ 6 2 (+₂ 2 4 (× 2 2 (from x) (from x₁)))
fromTest (C x) = +₂ 6 2 (from x)

test : Fin 4 -> Test
test x with ⨂ 2 2 x
test .(× 2 2 i j) | is× i j = B (to i) (to j)

toTest : Fin 8 -> Test
toTest x = [ (\y -> [ (\z -> A $ to z) , test ] (⨁ 2 4 y) ) , (\y -> C $ to y) ] (⨁ 6 2 x)

--from-cong : Setoid._≈_ (setoid Test) I.=[ fromTest ]⇒ Setoid._≈_ (setoid (Fin 8))
--from-cong refl = refl

from-preserves-eq : setoid Test ⟶ setoid (Fin 8)
from-preserves-eq = record { _⟨$⟩_ = fromTest ; cong = (\{ {i} {.i} refl → refl }) }

from-injective : Injective from-preserves-eq
from-injective {A x} {A x₁} p with from-bool-injective ∘ +-eq₁ ∘ +-eq₁ $ p
from-injective {A x} {A .x} p | refl = refl 
from-injective {A x} {B x₁ x₂} p = contradiction (+-eq₁ p) ¬+-eq₁
from-injective {A x} {C x₁} p = contradiction p ¬+-eq₁
from-injective {B x x₁} {A x₂} p = contradiction (+-eq₁ p) ¬+-eq₂
from-injective {B x x₁} {B y y₁} p with +-eq₂ {2} {4} ∘ +-eq₁ $ p
... | p2 with from-bool-injective (×-equal₁ {x₁ = x} {x₂ = y} p2) | ×-equal₂ {x₁ = x} {x₂ = y} p2
from-injective {B x x₁} {B .x .x₁} p | p2 | refl | refl = refl
from-injective {B x x₁} {C x₂} p = contradiction p ¬+-eq₁
from-injective {C x} {A x₁} p = contradiction p ¬+-eq₂
from-injective {C x} {B x₁ x₂} p = contradiction p ¬+-eq₂
from-injective {C x} {C .x} refl = refl

from-surjective : Surjective from-preserves-eq
from-surjective = record { from = preserves-eq-inv ; right-inverse-of = inv }
  where
--    cong-inverse : Setoid._≈_ (setoid (Fin 8)) I.=[ toTest ]⇒ Setoid._≈_ (setoid Test)
--    cong-inverse refl = refl
    
    preserves-eq-inv : setoid (Fin 8) ⟶ setoid Test
    preserves-eq-inv = record { _⟨$⟩_ = toTest ; cong = (\{ {i} {.i} refl → refl }) }
    
    inv : preserves-eq-inv RightInverseOf from-preserves-eq
    inv x with ⨁ 6 2 x
    inv .(+₁ 6 2 i) | is+₁ i with ⨁ 2 4 i
    inv ._ | is+₁ ._ | is+₁ i
      rewrite (Surjective.right-inverse-of (Bijective.surjective (Bijection.bijective (bijection {Bool})))) i = refl
    inv ._ | is+₁ ._ | is+₂ j with ⨂ 2 2 j
    inv ._ | is+₁ ._ | is+₂ ._ | is× i j 
      rewrite (Surjective.right-inverse-of (Bijective.surjective (Bijection.bijective (bijection {Fin 2})))) i
        | (Surjective.right-inverse-of (Bijective.surjective (Bijection.bijective (bijection {Bool})))) j = refl
    inv ._ | is+₂ j = refl
    
from-injection : Test ↣ Fin 8
from-injection = record { to = from-preserves-eq ; injective = from-injective }

from-surjection : Test ↠ Fin 8
from-surjection = record { to = from-preserves-eq ; surjective = from-surjective }

from-bijection : Bijection (setoid Test) (setoid (Fin 8))
from-bijection = record { to = from-preserves-eq ; bijective = record { injective = from-injective ; surjective = from-surjective } }

instance
  serializerTest : Serializer Test
  serializerTest = record {
    size = 8 ;
    from = fromTest ;
    to = toTest ;
    bijection = from-bijection
    }
