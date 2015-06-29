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
open import Function.Bijection using (Bijection ; id)
open import Relation.Nullary
open import Relation.Nullary.Negation

record Generic (T : Set) : Set where
  constructor generic
  field
    size : ℕ
    from` : T -> Fin size
    to` : Fin size -> T
    bijection : Bijection (setoid T) (setoid (Fin size))

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
    from` = \{ true → zero ; false → suc zero } ;
    to` = \{ zero → true ; (suc x) → false } ;
    bijection = bool-bijection }

  genFin : Generic (Fin 2)
  genFin = record {
    size = 2 ;
    from` = \{ x -> x } ;
    to` = \{ x -> x } ;
    bijection = Function.Bijection.id }

data Test : Set where
  A : Bool -> Test
  B : Fin 2 -> Test

open Generic {{...}}
 
from : Test -> Fin 4
from (A x) = inject+ 2 (from` x)
from (B x) = fromℕ 2 + (from` x)

to : Fin 4 -> Test
to zero = A true
to (suc zero) = A false
to (suc (suc x)) = B x
    
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

instance
  genTest : Generic Test
  genTest = record {
    size = 4 ;
    from` = from ;
    to` = to;
    bijection = from-bijection}
