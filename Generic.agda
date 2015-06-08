module Generic where

open import Agda.Primitive
open import Reflection
open import Data.Fin hiding (_+_)
open import Data.Nat
open import Data.List
open import Data.String
open import Data.Product using (_,_)
open import Data.Bool
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl ; cong)
open import Function using (_∘_ ; _$_ ; _∋_)

-------------------------
-- Term construction helpers.

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

-- Annotate terms with a type
_∋-t_ : Term -> Term -> Term
_∋-t_ ty term = def (quote _∋_) (a ty ∷ a term ∷ [])

-------------------------
-- Supported types.

supported_constr : Name -> Bool
supported_constr constr with type constr
supported constr constr | el s (def f []) = true
supported constr constr | x = false

supported : Name -> Bool
supported n with (definition n)
supported n | data-type d = and (map supported_constr (constructors d))
supported n | x = false

cons : (n : Name) -> List Name
cons n with (definition n)
cons n | data-type d = constructors d
cons n | _ = []

-------------------------
-- Generic from/to term's.

genFrom` : (n : Name) -> {_ : T $ supported n} -> Term
genFrom` n = fun_type ∋-t pat-lam clauses []
  where
    fun_type = pi (a ∘ t0 $ def n []) (abs "_" ∘ fin_type ∘ length ∘ cons $ n)
    
    clause` : (n : ℕ) -> Name -> Clause
    clause` idx c = clause [ a $ con c [] ] (fin_term idx)
    
    clauses = zipWith clause` (downFrom ∘ length ∘ cons $ n) (cons n)

genTo` : (n : Name) -> {_ : T $ supported n} -> Term
genTo` n = fun_type ∋-t pat-lam clauses []
  where
    fun_type = pi (a ∘ fin_type ∘ length ∘ cons $ n) (abs "_" ∘ t0 $ def n [])
    
    clause` : (n : ℕ) -> Name -> Clause
    clause` idx c = clause [ a $ fin_pat idx $ var "_" ] (con c [])
    
    clauses = zipWith clause` (downFrom ∘ length ∘ cons $ n) (cons n)

-------------------------
-- Generic from/to function definitions.

infer_type = el (lit 0) unknown

genFrom : (n : Name) -> {_ : T (supported n)} -> FunctionDef
genFrom n {s} = fun-def infer_type [ clause [] $ genFrom` n {s} ]

genTo : (n : Name) -> {_ : T (supported n)} -> FunctionDef
genTo n {s} = fun-def infer_type [ clause [] $ genTo` n {s} ]

-------------------------
-- Generic correctness proof ∀x to ∘ from x ≡ x

proofIso : (n n1 n2 : Name) -> {s : T (supported n)} -> FunctionDef
proofIso n n1 n2 {s} = fun-def (t0 fun_type) clauses
  where
    proof_type = def (quote _≡_) $ (a $ def n2 [ a $ def n1 [ a $ var 0 [] ] ]) ∷ (a $ var 0 []) ∷ []
    fun_type = pi (a ∘ t0 $ def n []) (abs "_" (t0 proof_type))
   
    clauses = map (\c -> clause [ a $ con c [] ] (con (quote refl) [])) (cons n) 

-------------------------
-- Generic from/to example.

data Test : Set where
  One : Test
  Two : Test
  Three : Test

unquoteDecl fromTest = genFrom (quote Test)
unquoteDecl toTest = genTo (quote Test)
unquoteDecl proofTest = proofIso (quote Test) (quote fromTest) (quote toTest)

----------------
-- meeting 26/05/15

-- beter supported met s

-- size : (n: Name) -> N
-- forall (fin (size n) -> genFrom (genTo)

-- relatie definieren tussen naam en types

-- macro-mechanisme

-- for all n -> Name -> term
-- ?

-- eindige constructren
-- geen recursie

-- voor pyware
  -- representatie als vector van bits



-- deriving eq
-- dec-eq-fin

-- unquoteDecl eq MFT x y = (genTo x) (genTo y)
-- dec_eq_fin
-- left x
-- right x

-- macro

-- vec n


----------------
-- meeting 02/06/15

-- unquoteDecl

-- type annotaties teoveogen
-- genereer bewijsterm met unquote decl
-- proberen ℕ
-- macro
-- proberen met type-annotaties
-- agda code bekijken naar reflectiemechaniscme
 
