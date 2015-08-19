module Generate where

open import Data.List
open import Data.Fin hiding (_+_)
open import Data.Nat
open import Data.Product
open import Data.Bool
open import Function using (_∘_ ; _$_ ; _∋_ ; id)
open import Function.Injection hiding (_∘_)
open import Function.Surjection hiding (_∘_)
open import Function.Bijection hiding (_∘_)
open import Function.LeftInverse hiding (_∘_)
open import Relation.Binary using (Setoid)
open import Relation.Binary.PropositionalEquality hiding ( [_] )
open import Relation.Nullary.Negation
open import Function.Equality using (_⟶_ ;  _⟨$⟩_ ; Π )
open import Reflection

open import Serializer
open import Helper.Fin
open import Helper.CodeGeneration

open import Serializer.Bool
open import Serializer.Fin

open Serializer.Serializer {{...}}
--open Serializer.Serializer {{Fin 2}}

-------------------------
-- Generic from/to term's.

data Test : Set where
  B : Bool -> Test
  A : Bool -> Test
--  C : Bool -> Test1
--  D : Bool -> Test1
  
conSize : (n : Name) -> Term
conSize n with (definition n)
conSize n | constructor′ with (type n)
conSize n | constructor′ | el (lit n₁) (pi (arg i (el s t)) t₂) = def (quote size) [ a1 t ]
conSize n | constructor′ | el _ _ = quoteTerm 0
conSize n | _ = quoteTerm 0

sumTerms : List Name -> Term
sumTerms [] = quoteTerm 0
sumTerms (x ∷ ls) = def (quote _+_) (a (conSize x) ∷ a (sumTerms ls) ∷ [])

cons`` : (n : Name) -> List (_×_ Name (_×_ (List Name) (List Name)))
cons`` n = zipWith _,_ (cons n) (zipWith _,_ (inits (cons n)) (drop 1 (tails (cons n))))

genFrom : (n : Name)  -> FunctionDef
genFrom n = fun-def infer_type [ (clause [] (fun_type ∋-t pat-lam clauses []) ) ]
  where
    fun_type = pi (a ∘ t0 $ def n []) (abs "_" (t0 (def (quote Fin) [ a (sumTerms (cons n)) ])))
  
    cons` = zipWith _,_ (cons n) (zipWith _,_ (inits (cons n)) (drop 1 (tails (cons n))))

    construct : (_×_ Name (_×_ (List Name) (List Name))) -> Term
    construct (c , [] , ys) = def (quote +₁) ((a (conSize c)) ∷ (a (sumTerms ys)) ∷ (a (def (quote from) [ a (var 0 []) ])) ∷ [])
    construct (c , x ∷ [] , ys) = def (quote +₂) ((a (conSize x)) ∷ (a (conSize c)) ∷ (a (def (quote from) [ a (var 0 []) ])) ∷ [])
    construct (c , x ∷ xs , ys) = def (quote +₂) ((a (conSize x)) ∷ (a (sumTerms (xs ++ [ c ] ++ ys))) ∷ (a (construct (c , (xs , ys)))) ∷ [])

    clauses = Data.List.map (\{ (c , xs) -> clause [ a $ con c [ a (var "_") ] ] (construct (c , xs))}) cons`

genTo : (n : Name)  -> FunctionDef
genTo n = fun-def infer_type [ (clause [] (fun_type ∋-t pat-lam clauses []) ) ]
  where
    fun_type = pi (a (t0 (def (quote Fin) [ a (sumTerms (cons n)) ]))) (abs "_" (t0 $ def n []))

    match : List Name -> Term
    match [] = {!!}
    match (x ∷ []) = con x [ a (def (quote to) [ a (var 0 []) ]) ]
    match (x ∷ x₁ ∷ cons) = def (quote [_,_]) ( (a (lam visible (abs "_" (con x [ a (def (quote to) [ a (var 0 []) ]) ])))) ∷ (a (lam visible (abs "_" (match (x₁ ∷ cons))))) ∷ [])

    clauses = [ clause [] (match (cons n)) ]
    
--unquoteDecl fromTest = genFrom (quote Test)
--unquoteDecl toTest = genTo (quote Test)

fromTest : Test -> Fin 4
fromTest (B x) = +₁ 2 2 (from x)
fromTest (A x) = +₂ 2 2 (from x)

toTest : Fin 4 -> Test
toTest x = Helper.Fin.[ (\y -> B $ to y) , (\y -> A $ to y) ] x

from-preserves-eq : setoid Test ⟶ setoid (Fin 4)
from-preserves-eq = record { _⟨$⟩_ = fromTest ; cong = (\{ {i} {.i} refl → refl }) }

{-
from-injective : Injective from-preserves-eq
from-injective = \ {
  {A x} {A y} p ->  (({y y₁ : Bool} -> (y ≡ y₁) -> (setoid Test Relation.Binary.Setoid.≈ A y) (A y₁)) ∋ (\{ {x} refl -> refl}))  (Bijective.injective (Bijection.bijective (bijection {Bool})) ∘ +-eq₁ $ p)
  ; {A x} {B x₁} p -> contradiction p ¬+-eq₁
  ; {B x} {A x₁} p -> contradiction p ¬+-eq₂
  ; {B x} {B x₁} p -> (({y y₁ : Bool} -> (y ≡ y₁) -> (setoid Test Relation.Binary.Setoid.≈ B y) (B y₁)) ∋ (\{ {x} refl -> refl}))  (Bijective.injective (Bijection.bijective (bijection {Bool})) ∘ (+-eq₂ {2} {2}) $ p)
 }

-}

from-surjective : Surjective from-preserves-eq
from-surjective = record { from = record { _⟨$⟩_ = toTest ; cong = (\{ {i} {.i} refl → refl }) } ; right-inverse-of = inv }
  where

    preserves-eq-inv : setoid (Fin 4) ⟶ setoid Test
    preserves-eq-inv = record { _⟨$⟩_ = toTest ; cong = (\{ {i} {.i} refl → refl }) }

{-
Goal: (setoid (Fin 4) Relation.Binary.Setoid.≈
       from-preserves-eq ⟨$⟩ (preserves-eq-inv ⟨$⟩ +₁ (suc 1) 2 i))
      (+₁ (suc 1) 2 i)

Goal: (setoid (Fin 4) Relation.Binary.Setoid.≈
       from-preserves-eq ⟨$⟩ (preserves-eq-inv ⟨$⟩ suc (suc j)))
      (suc (suc j))


Goal: (setoid (Fin 4) Relation.Binary.Setoid.≈
       from-preserves-eq ⟨$⟩ (preserves-eq-inv ⟨$⟩ x))
      x

Goal: suc (suc (fromBool (toBool j))) ≡ suc (suc j)
Goal: +₁ 2 2 (fromBool (toBool i)) ≡ +₁ (suc 1) 2 i

Goal: (λ { (A z) → +₁ 2 (2 + 0) (fromBool z)
         ; (B z) → +₂ 2 2 (fromBool z)
         })
      ([_,_] {Test} {2} {2} (λ z → A (toBool z)) (λ z → B (toBool z))
       (+₁ 2 2 i)
       | ⨁ 2 2 (+₁ 2 2 i))
      ≡ +₁ 2 2 i
-}

    inv : preserves-eq-inv RightInverseOf from-preserves-eq
    inv x = (({y : Fin 4} -> (Fin+ 2 2 y) -> (fromTest (toTest y)) ≡ y) ∋
      -- This doesn't typecheck...
      (\{ {._} (is+₁ i) → subst (\z -> +₁ 2 2 (fromBool (toBool i)) ≡ +₁ 2 2 z) (Surjective.right-inverse-of (Bijective.surjective (Bijection.bijective (bijection {Bool}))) i) refl ;
      -- This typechecks fine.
      {._} (is+₂ j) → subst (\z -> +₂ 2 2 (fromBool (toBool j)) ≡ +₂ 2 2 z) (Surjective.right-inverse-of (Bijective.surjective (Bijection.bijective (bijection {Bool}))) j) refl
      } )) (⨁ 2 2 x)

{-
    inv : preserves-eq-inv RightInverseOf from-preserves-eq
    inv x with ⨁ 2 2 x
    inv ._ | is+₁ i = subst (\z -> +₁ 2 2 (fromBool (toBool i)) ≡ +₁ 2 2 z) (Surjective.right-inverse-of (Bijective.surjective (Bijection.bijective (bijection {Bool}))) i) refl
    inv ._ | is+₂ j = subst (\z -> +₂ 2 2 (fromBool (toBool j)) ≡ +₂ 2 2 z) (Surjective.right-inverse-of (Bijective.surjective (Bijection.bijective (bijection {Bool}))) j) refl
-}

{-
    inv : preserves-eq-inv RightInverseOf from-preserves-eq
    inv x with ⨁ 2 2 x
    inv ._ | is+₁ i rewrite (Surjective.right-inverse-of (Bijective.surjective (Bijection.bijective (bijection {Bool})))) i = refl
    inv ._ | is+₂ j rewrite (Surjective.right-inverse-of (Bijective.surjective (Bijection.bijective (bijection {Bool})))) j = refl
-}

{-

from-bijection : Bijection (setoid Test) (setoid (Fin 4))
from-bijection = record {
    to = record { _⟨$⟩_ = fromTest ; cong = (\{ {i} {.i} refl → refl }) }
  ; bijective = record {
      injective = \ {
        {A x} {A y} p ->  (({y y₁ : Bool} -> (y ≡ y₁) -> (setoid Test Relation.Binary.Setoid.≈ A y) (A y₁)) ∋ (\{ {x} refl -> refl}))  (Bijective.injective (Bijection.bijective (bijection {Bool})) ∘ +-eq₁ $ p)
        ; {A x} {B x₁} p -> contradiction p ¬+-eq₁
        ; {B x} {A x₁} p -> contradiction p ¬+-eq₂
        ; {B x} {B x₁} p -> (({y y₁ : Bool} -> (y ≡ y₁) -> (setoid Test Relation.Binary.Setoid.≈ B y) (B y₁)) ∋ (\{ {x} refl -> refl}))  (Bijective.injective (Bijection.bijective (bijection {Bool})) ∘ (+-eq₂ {2} {2}) $ p)
    }
    ; surjective = record {
        from = record { _⟨$⟩_ = toTest ; cong = (\{ {i} {.i} refl → refl }) }
      ; right-inverse-of = {!!}
      }
    }
  }

-}
