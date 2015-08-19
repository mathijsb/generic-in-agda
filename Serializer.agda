module Serializer where

open import Data.List
open import Data.Fin hiding (_+_)
open import Data.Nat
open import Data.Product
open import Data.Bool
open import Function using (_∘_ ; _$_ ; _∋_)
open import Function.Injection hiding (_∘_)
open import Function.Surjection hiding (_∘_)
open import Function.Bijection hiding (_∘_)
open import Relation.Binary.PropositionalEquality hiding ( [_] )
open import Reflection

open import Helper.Fin
open import Helper.CodeGeneration

-----------------------------------
-- Generic
-----------------------------------

-- Finite

record Serializer (T : Set) : Set where
  constructor serializer
  field
    size : ℕ
    from : T -> Fin size
    to : Fin size -> T
    bijection : Bijection (setoid T) (setoid (Fin size))
