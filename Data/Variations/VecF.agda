module OTT.Data.Variations.VecF where

open import OTT.Main

caseℕ : ∀ {α} {A : Set α} -> A -> (ℕ -> A) -> ℕ -> A
caseℕ x f  0      = x
caseℕ x f (suc n) = f n

vec : ∀ {k} -> Univ k -> ℕ -> Type
vec A  0      = unit
vec A (suc n) = vec A n & A

Vec : ∀ {k} -> Univ k -> ℕ -> Set
Vec A n = ⟦ vec A n ⟧

[]ᵥ : ∀ {k} {A : Univ k} -> Vec A 0
[]ᵥ = triv

consᵥ : ∀ {k} {A : Univ k} n -> ⟦ A ⇒ vec A n ⇒ vec A (suc n) ⟧
consᵥ n x xs = xs , x

elimVec : ∀ {n k π} {A : Univ k}
        -> (P : ∀ n -> Vec A n -> Set π)
        -> (∀ {n} {xs : Vec A n} -> (x : ⟦ A ⟧) -> P n xs -> P (suc n) (consᵥ n x xs))
        -> P 0 ([]ᵥ {A = A})
        -> (xs : Vec A n)
        -> P n xs
elimVec {0}     P f z  triv    = z
elimVec {suc n} P f z (xs , x) = f x (elimVec P f z xs)
