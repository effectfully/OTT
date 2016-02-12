module OTT.Data.Vec where

open import OTT.Main

infixr 5 _∷ᵥ_

vec : ∀ {k} -> Univ k -> ℕ -> Type
vec A = rose $ (unit , λ _ -> [] , 0) ∷ ((nat & A) , λ p -> proj₁ p ∷ [] , suc (proj₁ p)) ∷ []

Vec : ∀ {k} -> Univ k -> ℕ -> Set
Vec A n = ⟦ vec A n ⟧

vnilₑ : ∀ {m k} {A : Univ k} -> ⟦ 0 ≅ m ⇒ vec A m ⟧
vnilₑ q = node $ 0 # , [] , q

vconsₑ : ∀ {n m k} {A : Univ k} -> ⟦ suc n ≅ m ⇒ A ⇒ vec A n ⇒ vec A m ⟧
vconsₑ {n} q x xs = node $ 1 # (n , x) , xs ∷ [] , q

[]ᵥ : ∀ {k} {A : Univ k} -> Vec A 0
[]ᵥ = vnilₑ (refl 0)

_∷ᵥ_ : ∀ {n k} {A : Univ k} -> ⟦ A ⇒ vec A n ⇒ vec A (suc n) ⟧
_∷ᵥ_ {n} = vconsₑ (refl (suc n))

elimVecₑ : ∀ {n k π} {A : Univ k}
         -> (P : ∀ {n} -> Vec A n -> Set π)
         -> (∀ {n m} {xs : Vec A n}
               -> (q : ⟦ suc n ≅ m ⟧) -> (x : ⟦ A ⟧) -> P xs -> P {m} (vconsₑ q x xs))
         -> (∀ {m} -> (q : ⟦ 0 ≅ m ⟧) -> P {m} (vnilₑ q))
         -> (xs : Vec A n)
         -> P xs
elimVecₑ P f z (node (here  (, [] , q)))                    = z q
elimVecₑ P f z (node (there (here ((n , x), xs ∷ [] , q)))) = f q x (elimVecₑ P f z xs)
elimVecₑ P f z (node (there (there ())))

foldVec : ∀ {n k π} {A : Univ k} {P : Set π} -> (⟦ A ⟧ -> P -> P) -> P -> Vec A n -> P
foldVec f z = elimVecₑ _ (const f) (const z)

fromVec : ∀ {n k} {A : Univ k} -> Vec A n -> List ⟦ A ⟧
fromVec = foldVec _∷_ []

elimVec′ : ∀ {n k π} {A : Univ k}
         -> (P : List ⟦ A ⟧ -> Set π)
         -> (∀ {n} {xs : Vec A n} -> (x : ⟦ A ⟧) -> P (fromVec xs) -> P (x ∷ fromVec xs))
         -> P []
         -> (xs : Vec A n)
         -> P (fromVec xs)
elimVec′ P f z = elimVecₑ (P ∘ fromVec) (λ {n m xs} _ -> f {xs = xs}) (const z)

elimVec : ∀ {n k s} {A : Univ k}
        -> (P : ∀ {n} -> Vec A n -> Univ s)
        -> (∀ {n} {xs : Vec A n} -> (x : ⟦ A ⟧) -> ⟦ P xs ⇒ P (x ∷ᵥ xs) ⟧)
        -> ⟦ P []ᵥ ⟧
        -> (xs : Vec A n)
        -> ⟦ P xs ⟧
elimVec P f z = elimVecₑ (⟦_⟧ ∘ P)
  (λ {n m xs} q x r -> subst₂ (λ m q -> P {m} (vconsₑ q x xs)) q (huip (suc n) m q) (f x r))
  (λ {m}      q     -> subst₂ (λ m q -> P {m} (vnilₑ q))       q (huip 0 m q)        z)
