module With where

open import Reflection
open import Function using (_∘_ ; _$_ ; _∋_ ; id ; const)
open import Data.List
open import Data.Nat hiding (_+_)
open import Relation.Binary using (Setoid ; Decidable)
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality hiding ( [_] ; subst )

open import Helper.CodeGeneration

{-# TERMINATING #-}
mutual

  s_arg : (n : ℕ) -> (ℕ -> Term -> Term) -> Arg Term -> Arg Term
  s_arg n f (arg i x) = arg i (s_term' n f x)

  s_type : (n : ℕ) -> (ℕ -> Term -> Term) -> Type -> Type
  s_type n f (el s t) = el s (s_term' n f t)

  s_term : (n : ℕ) -> (ℕ -> Term -> Term) -> Term -> Term
  s_term n f (var x args) = var x (map (s_arg n f) args)
  s_term n f (con c args) = con c (map (s_arg n f) args)
  s_term n f (def f₁ args) = def f₁ (map (s_arg n f) args)
  s_term n f (lam v (abs s x)) = lam v (abs s (s_term' n f x))
  s_term n f (pat-lam cs args) = pat-lam cs (map (s n arg f) args)
  s_term n f (pi (arg i x) (abs s x₁)) = pi (arg i (s_type n f x)) (abs s (s_type n f x₁))
  s_term n f t = t

  s_term' : (n : ℕ) -> (ℕ -> Term -> Term) -> Term -> Term
  s_term' n f t = f n (s_term n f t)

inc_debruijn_indices : Term -> Term
inc_debruijn_indices t = s_term' zero alg t
  where
    alg : ℕ -> Term -> Term
    alg n (var x args) = var (suc x) args
    alg n t2 = t2
    
subst : Term -> Term -> Term -> Term
subst t ti to = s_term' zero alg t
  where
    alg : ℕ -> Term -> Term
    alg n ti1 with ti Reflection.≟ ti1
    alg n ti1 | yes p = to
    alg n ti1 | no ¬p = ti1
    
getType : {T : Set} -> (t : T) -> Term
getType {T} t = quoteTerm T

with' : Term -> Term -> Term
with' w l = quote-goal (abs "g" lam_body)
  where    
    sub_term = def (quote subst) ( (a $ var 1 []) ∷ (a $ w) ∷ (a $ quote-term $ var 0 []) ∷ [] )
    lam_type_q = unquote-term sub_term []
    lam_type = pi (a $ t0 unknown) (abs "i" $ t0 $ lam_type_q)
    lam_body = def (quote _$_) ((a $ lam_type ∋-t l) ∷ (a $ inc_debruijn_indices $ unquote-term w []) ∷ [])

postulate
   A     : Set
   _+_   : A → A → A
   T     : A → Set
   mkT   : ∀ x → T x
   P     : ∀ x → T x → Set

-- the type A of the with argument has no free variables, so the with
-- argument will come first
f₁ : (x y : A) (t : T (x + y)) → T (x + y)
f₁ x y t with x + y
f₁ x y t    | w = mkT w

f₂ : (x y : A) → T (x + y)
f₂ x y = unquote (with' (quoteTerm (quoteTerm (x + y))) (quoteTerm (\w -> mkT w)))
 

  -- def (quote inc_var_indices) [ a $ var 1 [] ] --
    -- sub_term = def (quote subst) ( (a $ var 1 []) ∷ (a $ w) ∷ (a $ (quote-term (var 0 []))) ∷ [] )
    -- lam_type = pi (a $ t0 $ (def (quote _≡_) ((a $ var 3 []) ∷ (a $ var 2 []) ∷ []))) (abs "i" $ t0 $ lam_type_q)

