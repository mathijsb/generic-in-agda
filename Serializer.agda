module Serializer where

open import Data.Fin hiding (_+_)
open import Data.Nat
open import Function.Injection
open import Function.Surjection
open import Function.Bijection
open import Relation.Binary.PropositionalEquality

open import Helper.Fin

-----------------------------------
-- Generic
-----------------------------------

record Serializer (T : Set) : Set where
  constructor serializer
  field
    size : ℕ
    from : T -> Fin size
    to : Fin size -> T
    bijection : Bijection (setoid T) (setoid (Fin size))
