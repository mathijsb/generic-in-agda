module Serializer.Bool where

open import Data.Bool
open import Data.Fin hiding (_+_)
open import Data.Nat
open import Relation.Binary
open import Relation.Binary.EqReasoning
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl ; cong ; setoid )
import Relation.Binary.Indexed as I
open import Function.Equality using (_⟶_ ;  _⟨$⟩_ ; Π )
open import Function.LeftInverse hiding (_∘_)
open import Function.Injection
open import Function.Surjection
open import Function.Bijection

open import Serializer

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
  serializerBool : Serializer Bool
  serializerBool = record {
    size = 2 ;
    from = fromBool ;
    to = toBool ;
    bijection = bool-bijection }
