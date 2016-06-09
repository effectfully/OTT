module OTT.Data.Vec where

open import OTT.Main

infixr 5 _∷ᵥ_

vec : ∀ {a} -> Type a -> ℕ -> Type a
vec A = icmu
      $ var 0
      ∷ (πᵈ nat λ n -> A ⇒ᵈ var n ⊛ var (suc n))
      ∷ []

Vec : ∀ {a} -> Type a -> ℕ -> Set
Vec A n = ⟦ vec A n ⟧

pattern vnilₑ      q      = #₀ q
pattern vconsₑ {n} q x xs = !#₁ (n , x , xs , q)

[]ᵥ : ∀ {a} {A : Type a} -> Vec A 0
[]ᵥ = vnilₑ (refl 0)

_∷ᵥ_ : ∀ {n a} {A : Type a} -> ⟦ A ⇒ vec A n ⇒ vec A (suc n) ⟧
_∷ᵥ_ {n} = vconsₑ (refl (suc n))

{-# TERMINATING #-}
elimVecₑ : ∀ {n a π} {A : Type a}
         -> (P : ∀ {n} -> Vec A n -> Set π)
         -> (∀ {n m} {xs : Vec A n}
               -> (q : ⟦ suc n ≅ m ⟧) -> (x : ⟦ A ⟧) -> P xs -> P {m} (vconsₑ q x xs))
         -> (∀ {m} -> (q : ⟦ 0 ≅ m ⟧) -> P {m} (vnilₑ q))
         -> (xs : Vec A n)
         -> P xs
elimVecₑ P f z (vnilₑ  q)      = z q
elimVecₑ P f z (vconsₑ q x xs) = f q x (elimVecₑ P f z xs)

foldVec : ∀ {n a π} {A : Type a} {P : Set π} -> (⟦ A ⟧ -> P -> P) -> P -> Vec A n -> P
foldVec f z = elimVecₑ _ (const f) (const z)

fromVec : ∀ {n a} {A : Type a} -> Vec A n -> List A
fromVec = foldVec _∷_ []

elimVec′ : ∀ {n a π} {A : Type a}
         -> (P : List A -> Set π)
         -> (∀ {n} {xs : Vec A n} -> (x : ⟦ A ⟧) -> P (fromVec xs) -> P (x ∷ fromVec xs))
         -> P []
         -> (xs : Vec A n)
         -> P (fromVec xs)
elimVec′ P f z = elimVecₑ (P ∘ fromVec) (λ {n m xs} _ -> f {xs = xs}) (const z)

elimVec : ∀ {n a p} {π : Level p} {A : Type a}
        -> (P : ∀ {n} -> Vec A n -> Univ π)
        -> (∀ {n} {xs : Vec A n} -> (x : ⟦ A ⟧) -> ⟦ P xs ⇒ P (x ∷ᵥ xs) ⟧)
        -> ⟦ P []ᵥ ⟧
        -> (xs : Vec A n)
        -> ⟦ P xs ⟧
elimVec P f z = elimVecₑ (⟦_⟧ ∘ P)
  (λ {n m xs} q x r -> J (λ m q -> P {m} (vconsₑ q x xs)) (f x r) q)
  (λ {m}      q     -> J (λ m q -> P {m} (vnilₑ q)) z q)
