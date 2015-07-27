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
open import Relation.Binary
open import Relation.Binary.EqReasoning
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl ; cong ; setoid)
import Relation.Binary.Indexed as I
open import Function using (_∘_ ; _$_ ; _∋_ ; id ; const)
open import Function.Equality using (_⟶_ ;  _⟨$⟩_ ; Π )
open import Function.LeftInverse hiding (_∘_)
open import Function.Injection using (_↣_ ; Injective ; Injection)
open import Function.Surjection using (_↠_ ; Surjective ; Surjection)
open import Function.Bijection using (Bijection ; Bijective ; id )
open import Relation.Nullary
open import Relation.Nullary.Negation

-----------------------------------
-- Fin magic
-----------------------------------

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

-----------------------------------
-- Generic
-----------------------------------

record Generic (T : Set) : Set where
  constructor generic
  field
    size : ℕ
    from : T -> Fin size
    to : Fin size -> T
    bijection : Bijection (setoid T) (setoid (Fin size))

-----------------------------------
-- Generic instances for Bool & Fin
-----------------------------------

fromBool : Bool -> Fin 2
fromBool true = zero
fromBool false = suc zero

toBool : Fin 2 -> Bool
toBool zero = true
toBool (suc x) = false

bool-cong : Setoid._≈_ (setoid Bool) I.=[ fromBool ]⇒ Setoid._≈_ (setoid (Fin 2))
bool-cong refl = refl

bool-cong-inv : Setoid._≈_ (setoid (Fin 2)) I.=[ toBool ]⇒ Setoid._≈_ (setoid (Bool))
bool-cong-inv refl = refl

from-bool-preserves-eq : setoid Bool ⟶ setoid (Fin 2)
from-bool-preserves-eq = record { _⟨$⟩_ = fromBool ; cong = bool-cong }

from-bool-injective : Injective from-bool-preserves-eq
from-bool-injective {true} {true} refl = refl
from-bool-injective {true} {false} ()
from-bool-injective {false} {true} ()
from-bool-injective {false} {false} refl = refl

bool-preserves-eq-inv : setoid (Fin 2) ⟶ setoid Bool
bool-preserves-eq-inv = record { _⟨$⟩_ = toBool ; cong = bool-cong-inv }

bool-inv : bool-preserves-eq-inv RightInverseOf from-bool-preserves-eq
bool-inv zero = refl
bool-inv (suc zero) = refl
bool-inv (suc (suc ()))

from-bool-surjective : Surjective from-bool-preserves-eq
from-bool-surjective = record { from = bool-preserves-eq-inv ; right-inverse-of = bool-inv   }

bool-bijection : Bijection (setoid Bool) (setoid (Fin 2))
bool-bijection = record { to = from-bool-preserves-eq ; bijective = record { injective =  from-bool-injective ; surjective = from-bool-surjective } }

instance
  genBool : Generic Bool
  genBool = record {
    size = 2 ;
    from = fromBool ;
    to = toBool ;
    bijection = bool-bijection }

  genFin : ∀ {n} -> Generic (Fin n)
  genFin {n} = record {
    size = n ;
    from = Function.id ;
    to = Function.id ;
    bijection = Function.Bijection.id }

-----------------------------------
-- Generic instance for Test
-----------------------------------

data Test : Set where
  A : Bool -> Test
  B : Fin 2 -> Bool -> Test
  C : Fin 2 -> Test

open Generic {{...}}

fromTest : Test -> Fin ((2 + (2 * 2)) + 2)
fromTest (A x) = +₁ 6 2 (+₁ 2 4 (from x))
fromTest (B x x₁) = +₁ 6 2 (+₂ 2 4 (× 2 2 (from x) (from x₁)))
fromTest (C x) = +₂ 6 2 (from x)

test : Fin 4 -> Test
test x with ⨂ 2 2 x
test .(× 2 2 i j) | is× i j = B (to i) (to j)

toTest : Fin 8 -> Test
toTest x = [ (\y -> [ (\z -> A $ to z) , test ] y ) , (\y -> C $ to y) ] x

lemma : {x x₁ : Bool} -> fromTest (A x) ≡ fromTest (A x₁) -> x ≡ x₁
lemma {true} {true} p = refl
lemma {true} {false} ()
lemma {false} {true} ()
lemma {false} {false} p = refl

lemma₁ : {n : ℕ} {x x₁ : Fin n} -> Data.Fin.suc (Data.Fin.suc x) ≡ Data.Fin.suc (Data.Fin.suc x₁) -> x ≡ x₁
lemma₁ {ℕ.zero} refl = refl
lemma₁ {ℕ.suc n} refl = refl

from-cong : Setoid._≈_ (setoid Test) I.=[ fromTest ]⇒ Setoid._≈_ (setoid (Fin 8))
from-cong refl = refl

from-preserves-eq : setoid Test ⟶ setoid (Fin 8)
from-preserves-eq = record { _⟨$⟩_ = fromTest ; cong = from-cong }


suc-eq : {n : ℕ} {x x₁ : Fin n} -> ((Data.Fin.suc x) ≡ (Data.Fin.suc x₁)) -> (x ≡ x₁)
suc-eq refl = refl

+-eq : {n n₁ : ℕ} {x x₁ : Fin n} -> (m : Fin n₁) -> ((m Data.Fin.+ x) ≡ (m Data.Fin.+ x₁)) -> (x ≡ x₁)
+-eq zero p = p
+-eq (suc m) p = +-eq m (suc-eq p)

¬+-eq₁ : {n m : ℕ} {x : Fin n} {y : Fin m} -> ¬( (+₁ n m) x ≡ (+₂ n m) y)
¬+-eq₁ {zero} {zero} {()}
¬+-eq₁ {zero} {suc m} {()}
¬+-eq₁ {suc n} {zero} {y = ()}
¬+-eq₁ {suc n} {suc m} {zero} ()
¬+-eq₁ {suc n} {suc m} {suc x} {zero} p = {!!}
¬+-eq₁ {suc n} {suc m} {suc x} {suc y} p with ¬+-eq₁ {n} {suc m} {x} {suc y}
... | p1 = {!!}

¬+-eq₂ : {n m : ℕ} {x : Fin n} {y : Fin m} -> ¬( (+₂ n m) y ≡ (+₁ n m) x)
¬+-eq₂ = {!!}

×-equal₁ : ∀ {n m : ℕ} {x₁ x₂ : Fin n} {y₁ y₂ : Fin m} -> (× n m x₁ y₁) ≡ (× n m x₂ y₂) -> (y₁ ≡ y₂)
×-equal₁ {n} {m} {x₁} {x₂} {y₁} {y₂} p = {!!}

{-
×-equal₁ {x₁ = zero} {zero} {zero} {zero} refl = refl
×-equal₁ {x₁ = zero} {zero} {zero} {suc y₂} ()
×-equal₁ {x₁ = zero} {zero} {suc y₁} {zero} ()
×-equal₁ {x₁ = zero} {zero} {suc y₁} {suc y₂} p = cong suc (×-equal₁ {!!})
×-equal₁ {x₁ = zero} {suc x₂} p = {!!}
×-equal₁ {x₁ = suc x} {x₂} p = {!!}
-}

×-equal₂ : ∀ {n m : ℕ} {x₁ x₂ : Fin n} {y₁ y₂ : Fin m} -> (× n m x₁ y₁) ≡ (× n m x₂ y₂) -> (x₁ ≡ x₂)
×-equal₂ = {!!} 

+-eq₁ : {n n₁ : ℕ} {x x₁ : Fin n} -> (+₁ n n₁ x ≡ +₁ n n₁ x₁) -> (x ≡ x₁)
+-eq₁ {x = zero} {x₁ = zero} p = refl
+-eq₁ {x = zero} {suc x₁} ()
+-eq₁ {x = suc x} {zero} ()
+-eq₁ {x = suc x} {x₁ = suc x₁} p with +-eq (fromℕ 1) p
... | p1 with +-eq₁ p1
... | p2 = cong suc p2

+-eq₂ : {n n₁ : ℕ} {x x₁ : Fin n₁} -> (+₂ n n₁ x ≡ +₂ n n₁ x₁) -> (x ≡ x₁)
+-eq₂ {x = zero} {x₁ = zero} p = refl
+-eq₂ {zero} {x = zero} {suc x₁} p = p
+-eq₂ {suc n} {x = zero} {suc x₁} p = {!!} -- cong {!suc!} {!!}
+-eq₂ {x = suc x} {zero} p = {!!} 
+-eq₂ {x = suc x} {x₁ = suc x₁} p = {!!}

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
    cong-inverse : Setoid._≈_ (setoid (Fin 8)) I.=[ toTest ]⇒ Setoid._≈_ (setoid Test)
    cong-inverse refl = refl
    
    preserves-eq-inv : setoid (Fin 8) ⟶ setoid Test
    preserves-eq-inv = record { _⟨$⟩_ = toTest ; cong = cong-inverse }
    
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
  genTest : Generic Test
  genTest = record {
    size = 8 ;
    from = fromTest ;
    to = toTest ;
    bijection = from-bijection
    }
