module Helper.CodeGeneration where

open import Agda.Primitive
open import Data.Nat
open import Data.Fin
open import Data.List
open import Function using (_∘_ ; _$_ ; _∋_)
open import Reflection

a : {A : Set} -> (x : A) -> Arg A
a x = arg (arg-info visible relevant) x

a1 : {A : Set} -> (x : A) -> Arg A
a1 x = arg (arg-info hidden relevant) x

t0 : Term -> Type
t0 t = el (lit 0) t

fin_term : (n : ℕ) -> Term
fin_term zero = con (quote Fin.zero) []
fin_term (suc fin) = con (quote Fin.suc) [ a (fin_term fin) ]

fin_pat : (n : ℕ) -> (l : Pattern) -> Pattern
fin_pat zero l = l
fin_pat (suc n) l = con (quote Fin.suc) [ a (fin_pat n l) ]

fin_type : (n : ℕ) -> Type
fin_type n = t0 (def (quote Fin) [ a (lit (nat n)) ])

-- Annotate terms with a type
_∋-t_ : Term -> Term -> Term
_∋-t_ ty term = def (quote _∋_) (a ty ∷ a term ∷ [])

cons : (n : Name) -> List Name
cons n with (definition n)
cons n | data-type d = constructors d
cons n | _ = []

infer_type = el (lit 0) unknown
