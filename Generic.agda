module Generic where

open import Reflection
open import Data.Fin hiding (_+_)
open import Data.Nat
open import Data.List
open import Data.String
open import Data.Product using (_,_)
open import Data.Bool
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl ; cong)

data Test : Set where
  One : Test
  Two : Test
  Three : Test

a : {A : Set} -> (x : A) -> Arg A
a x = arg (arg-info visible relevant) x

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

data SupportedType : Set where
  supportedType : (cons : List Name) -> SupportedType
  unsupportedType : SupportedType
  
data UnsupportedType : Set where

supported_constr : Name -> Bool
supported_constr constr with type constr
supported constr constr | el s (def f []) = true
supported constr constr | x = false

supported : Name -> SupportedType
supported n with (definition n)
supported n | data-type d = let cons = constructors d in if (and (map supported_constr cons)) then supportedType cons else unsupportedType
supported n | x = unsupportedType

supported` : Name -> Set
supported` n with supported n
supported` n | supportedType cons = SupportedType
supported` n | unsupportedType = UnsupportedType

genFrom : (n : Name) -> FunctionDef
genFrom n with supported n
genFrom n | unsupportedType = fun-def (el unknown quote-context) [] -- raise error
genFrom n | supportedType cons = fun-def fun_type clauses
  where
    fun_type = t0 (pi (a (t0 (def n []))) (abs "_" (fin_type (length cons))))
    
    clause` : (n : ℕ) -> Name -> Clause
    clause` idx constr = clause [ a (con constr []) ] (fin_term idx)
    
    clauses = zipWith clause` (downFrom (length cons)) cons

genTo : (n : Name) -> FunctionDef
genTo n with supported n
genTo n | unsupportedType = fun-def (el unknown quote-context) [] -- raise error
genTo n | supportedType cons = fun-def fun_type clauses
  where
    fun_type = t0 (pi (a (fin_type (length cons))) (abs "_"  (t0 (def n []))))
    
    clause` : (n : ℕ) -> Name -> Clause
    clause` idx constr = clause [ a (fin_pat idx (var "_")) ] (con constr [])
    
    clauses = zipWith clause` (downFrom (length cons)) cons

    --absurd_clause = absurd-clause [ (a (fin_pat (suc ((length cons))) absurd)) ]

unquoteDecl fromTest = genFrom (quote Test) 
unquoteDecl toTest = genTo (quote Test)

p : {x : Test} -> (toTest (fromTest x)) ≡ x
p {One} = refl
p {Two} = refl
p {Three} = refl

--p1 : {n : Name} -> {x : (unquote n)} -> (supported` n) -> (genTo (genFrom n)) ≡ x
--p1 = ?
