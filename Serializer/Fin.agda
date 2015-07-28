module Serializer.Fin where

open import Data.Fin hiding (_+_)
open import Data.Nat
open import Function using (_∘_ ; _$_ ; _∋_ ; id ; const)
open import Function.Bijection
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl ; cong ; setoid )

open import Serializer

instance
  serializerFin : ∀ {n} -> Serializer (Fin n)
  serializerFin {n} = record {
    size = n ;
    from = Function.id ;
    to = Function.id ;
    bijection = Function.Bijection.id }

