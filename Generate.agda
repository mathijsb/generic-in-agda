module Generate where

open import Data.List
open import Data.Fin hiding (_+_)
open import Data.Nat
open import Data.Product
open import Data.Bool
open import Function using (_∘_ ; _$_ ; _∋_ ; id ; case_return_of_ ; flip )
open import Function.Injection hiding (_∘_)
open import Function.Surjection hiding (_∘_)
open import Function.Bijection hiding (_∘_)
open import Function.LeftInverse hiding (_∘_)
open import Relation.Binary using (Setoid ; Decidable)
open import Relation.Binary.PropositionalEquality hiding ( [_] )
open import Relation.Nullary.Negation
open import Relation.Nullary
open import Function.Equality using (_⟶_ ;  _⟨$⟩_ ; Π )
open import Reflection
open import Level

open import Serializer
open import Helper.Fin
open import Helper.CodeGeneration

open import Serializer.Bool
open import Serializer.Fin
open import With hiding (subst) --  ; _+_ ; A)

open Serializer.Serializer {{...}}
--open Serializer.Serializer {{Fin 2}}

-------------------------
-- Generic from/to term's.

data Test : Set where
  A : Bool -> Test
  B : Bool -> Test
  C : Bool -> Test
  D : Bool -> Test

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


{-
fromTest : Test -> Fin 4
fromTest (A z) = +₁ 2 (2 + 0) (fromBool z)
fromTest (B z) = +₂ 2 2 (fromBool z)

toTest : Fin 4 -> Test
toTest x = (Helper.Fin.[ (λ z₁ → A (toBool z₁)) , (λ z₁ → B (toBool z₁)) ] (⨁ 2 2 x))
-}

{-
fromTest : Test -> Fin 6
fromTest (A x) = +₁ 4 2 (+₁ 2 2 (from x))
fromTest (B x) = +₁ 4 2 (+₂ 2 2 (from x))
fromTest (C x) = +₂ 4 2 (from x)

toTest : Fin 6 -> Test
toTest x = Helper.Fin.[ (\y -> Helper.Fin.[ (\z -> A $ to z) , (\z -> B $ to z) ] (⨁ 2 2 y) ) , (\y -> C $ to y) ] (⨁ 4 2 x)
-}

cons` : Name -> List (_×_ Name (_×_ (List Name) (List Name)))
cons` n = zipWith _,_ (reverse (cons n)) (zipWith _,_ (inits (reverse (cons n))) (Data.List.map reverse (drop 1 (tails (reverse (cons n))))))

{-# TERMINATING #-}
genFrom : (n : Name)  -> FunctionDef
genFrom n = fun-def (t0 $ fun_type) clauses
  where
    fun_type = pi (a ∘ t0 $ def n []) (abs "_" (t0 (def (quote Fin) [ a (sumTerms (cons n)) ])))
    
    construct : (_×_ Name (_×_ (List Name) (List Name))) -> Term
    construct (c , [] , []) = (def (quote from) [ a (var 0 []) ])
    construct (c , x ∷ xs , []) = def (quote +₂) ((a (sumTerms (x ∷ xs))) ∷ (a (conSize c)) ∷ (a (construct (c , ([] , [])))) ∷ [])
    construct (c , xs , y ∷ ys) = def (quote +₁) ((a (sumTerms (c ∷ (xs ++ ys)))) ∷ (a (conSize y)) ∷ (a (construct (c , (xs , ys)))) ∷ [])
    
    clauses = Data.List.map (\{ (c , xs) -> clause [ a $ con c [ a (var "_") ] ] (construct (c , xs))}) (cons` n)

unquoteDecl fromTest = genFrom (quote Test)

genTo : (n : Name)  -> FunctionDef
genTo n = fun-def (t0 $ fun_type) clauses
  where
    fun_type = pi (a (t0 (def (quote Fin) [ a (sumTerms (cons n)) ]))) (abs "_" (t0 $ def n []))

    match : List Name -> Term
    match [] = unknown
    match (x ∷ []) = con x [ a (def (quote to) [ a (var 0 []) ]) ]
    match (x ∷ x₁ ∷ cons) = def (quote [_,_])
          ( (a (lam visible (abs "_" (match (x₁ ∷ cons))))) -- (a (lam visible (abs "_" (con x [ a (def (quote to) [ a (var 0 []) ]) ]))))
          ∷ (a (lam visible (abs "_" (con x [ a (def (quote to) [ a (var 0 []) ]) ]))))
          ∷ (a (def (quote ⨁) ((a (sumTerms (x₁ ∷ cons))) ∷ (a (quoteTerm 2)) ∷ (a (var 0 [])) ∷ [])))
          ∷ [])

    clauses = [ clause [ a (var "_") ] (match (cons n)) ]

unquoteDecl toTest = genTo (quote Test)

makePresEq : {T : Set} {n : ℕ} -> (T -> (Fin n)) -> setoid T ⟶ setoid (Fin n)
makePresEq f = record { _⟨$⟩_ = f ; cong = (\{ {i} {.i} refl → refl }) }

genPresEq' : (n : Name) -> Term
genPresEq' n = def (quote makePresEq) [ a (def (quote fromTest) []) ] -- [(a (genFrom' n))]
  where
    setoidFrom = def (quote setoid) [(a (def n []))] 
    setoidTo = def (quote setoid) [(a (def (quote Fin) [ a (sumTerms (cons n)) ]))]
    fun_type1 = t0 (def (quote _⟶_) ( (a setoidFrom) ∷ (a setoidTo) ∷ []))
    
genPresEq : (n : Name) -> FunctionDef
genPresEq n = fun-def fun_type1 [(clause [] (genPresEq' n) ) ]
  where
    setoidFrom = def (quote setoid) [(a (def n []))] 
    setoidTo = def (quote setoid) [(a (def (quote Fin) [ a (sumTerms (cons n)) ]))]    
    fun_type1 = t0 (def (quote _⟶_) ( (a setoidFrom) ∷ (a setoidTo) ∷ []))

unquoteDecl genTest = genPresEq (quote Test)

t2 : {x y : Bool} → fromBool x ≡ fromBool y → x ≡ y
t2 = Bijective.injective (Bijection.bijective (bijection {Bool}))

bijection' : Term
bijection' = quoteTerm t2

refl' : Term
refl' = pat-lam [ clause ( (a1 (var "d1")) ∷ (a1 (dot)) ∷ ( a (con (quote refl) []) ) ∷ []) (con (quote refl) []) ] []

x₁≡x₂' : Term
x₁≡x₂' = def (quote _≡_) ((a $ var 1 []) ∷ (a $ var 0 []) ∷ [])

+-eq₁' : Term -> Term
+-eq₁' t = (def (quote +-eq₁) [ a t ])

+-eq₂' : ℕ -> ℕ -> Term -> Term
+-eq₂' n1 n2 t = (def (quote +-eq₂) ( a1 (lit (nat n1)) ∷ a1 (lit (nat n2)) ∷ a t ∷ [] ) )

¬+-eq₁' : Term
¬+-eq₁' = def (quote ¬+-eq₁) []

¬+-eq₂' : Term
¬+-eq₂' = def (quote ¬+-eq₂) []

_$'_ : Term -> Term -> Term
x $' y = def (quote _$_) ((a x) ∷ (a y) ∷ [])

contradiction' : Term -> Term -> Term
contradiction' t1 t2 = def (quote contradiction) ( (a t1) ∷ (a t2) ∷ [] )

genInjective : (n : Name) -> FunctionDef
genInjective n = fun-def fun_type1 [ (clause [] ( pat-lam (clauses 0 (var 0 []) (indexed_cons)) [] )) ]
  where
    fun_type1 = t0 (def (quote Injective) [ (a (def (quote genTest) [])) ] )

    ncons = (length (cons n))
    indexed_cons = zipWith (_,_) (cons n) ((downFrom (length (cons n))))

    clause'' : Name -> Name -> Term -> Clause
    clause'' l r t = clause ( (a1 $ con l [ a (var "x") ]) ∷ (a1 $ con r [ a (var "y") ]) ∷ (a (var "p")) ∷ [] ) t

    clause' : ℕ -> Term -> (_×_ Name ℕ) -> (_×_ Name ℕ) -> Clause
    clause' n t (n1 , i1) (n2 , i2) with (Data.Nat.compare i1 i2)
    clause' n t (n1 , i1) (n2 , ._) | less .i1 k = clause'' n1 n2 (contradiction' (t) ¬+-eq₁')
    clause' n t (n1 , ℕ.zero) (n2 , .0) | equal .0 = clause'' n1 n2 (with' x₁≡x₂' (bijection' $' (t)) refl')
    clause' n t (n1 , ℕ.suc i1) (n2 , .(ℕ.suc i1)) | equal .(ℕ.suc i1) = clause'' n1 n2 (with' x₁≡x₂' (bijection' $' (+-eq₂' ((ncons ∸ n ∸ 1) * 2) 2 (t))) refl')
    clause' n t (n1 , ._) (n2 , i2) | greater .i2 k = clause'' n1 n2 (contradiction' (t) ¬+-eq₂')
    
    clauses : ℕ -> Term -> List (_×_ Name ℕ) -> List Clause
    clauses n t [] = []
    clauses n t (x ∷ cs) = (Data.List.map (clause' n t x) (x ∷ cs)) ++ (Data.List.map ((flip (clause' n t)) x) cs) ++ (clauses (ℕ.suc n) (+-eq₁' t) cs) -- Data.List.map clause' c
    
unquoteDecl testInjective = genInjective (quote Test)

makePresEqTo : {T : Set} {n : ℕ} -> ((Fin n) -> T) -> setoid (Fin n) ⟶ setoid T
makePresEqTo f = record { _⟨$⟩_ = f ; cong = (\{ {i} {.i} refl → refl }) }

genPresEqTo' : (n : Name) -> Term
genPresEqTo' n = def (quote makePresEqTo) [ a (def (quote toTest) []) ]
  where
    setoidTo = def (quote setoid) [(a (def n []))] 
    setoidFrom = def (quote setoid) [(a (def (quote Fin) [ a (sumTerms (cons n)) ]))]
    fun_type1 = t0 (def (quote _⟶_) ( (a setoidFrom) ∷ (a setoidTo) ∷ []))

genPresEqTo : (n : Name) -> FunctionDef
genPresEqTo n = fun-def infer_type [ (clause [] (genPresEqTo' n) ) ]
    
unquoteDecl genTestTo = genPresEqTo (quote Test)

Fin+' : ℕ -> ℕ -> Term
Fin+' n1 n2 = def (quote Fin+) ((a (lit (nat n1))) ∷ (a (lit (nat n2))) ∷ (a $ var 0 []) ∷ [])

⨁' : ℕ -> ℕ -> Term
⨁' n1 n2 = def (quote ⨁) ((a (lit (nat n1))) ∷ (a (lit (nat n2))) ∷ (a $ var 0 []) ∷ [])

x₂≡x₁' : Term
x₂≡x₁' = def (quote _≡_) ( (a $ var 0 []) ∷ (a $ var 1 []) ∷ [])

right-inverse-of' : Term
right-inverse-of' = quoteTerm (Surjective.right-inverse-of (Bijective.surjective (Bijection.bijective (bijection {Bool}))))

fromToBool' : Term
fromToBool' = (def (quote fromBool) (arg (arg-info visible relevant) (def (quote toBool) (arg (arg-info visible relevant) (var 0 []) ∷ [])) ∷ []))

matchFin+ : Term -> Term -> Term
matchFin+ t1 t2 = pat-lam ((clause ( (a1 (dot)) ∷ (a (con (quote is+₁) [ a $ (var "u") ])) ∷ []) t1) ∷ (clause ( (a1 (dot)) ∷ (a (con (quote is+₂) [ a $ (var "u") ])) ∷ []) t2) ∷ []) []

step2 : Term
step2 = rewrite'' x₂≡x₁' (quoteTerm fromToBool') (quoteTerm (right-inverse-of' $' var 0 [])) refl'

⨁'' : ℕ -> ℕ -> Term
⨁'' m1 m2 = With.subst (quoteTerm (⨁' 1337 2)) (lit (nat 1337)) (lit (nat m1))

genRightInv' : (List Name) -> Term
genRightInv' [] = unknown
genRightInv' (x ∷ []) = step2
genRightInv' (x ∷ x₁ ∷ cons) = with'' (Fin+' l 2) (⨁'' l 2) (matchFin+ (genRightInv' (x₁ ∷ cons)) step2)
  where
    l = (length (x₁ ∷ cons) * 2)

right-inverse-of : genTestTo RightInverseOf genTest
right-inverse-of x = unquote (genRightInv' (cons (quote Test)))


{-
from-bijection : Bijection (setoid Test) (setoid (Fin 6))
from-bijection = record {
    to = genTest
  ; bijective = record {
      injective = testInjective
    ; surjective = record {
        from = genTestTo
      ; right-inverse-of = right-inverse-of
      }
    }
  }

instance
  serializerTest : Serializer Test
  serializerTest = record {
    size = 6 ;
    from = fromTest ;
    to = toTest ;
    bijection = from-bijection
    }
-}
