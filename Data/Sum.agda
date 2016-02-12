module OTT.Data.Sum where

open import OTT.Main

_⊕_ : ∀ {k s} -> Univ k -> Univ s -> Type
A ⊕ B = rose (((unit & A) , λ _ -> [] , triv) ∷ ((unit & B) , λ _ -> [] , triv) ∷ []) triv

_⊎_ : ∀ {k s} -> Univ k -> Univ s -> Set
A ⊎ B = ⟦ A ⊕ B ⟧

inj₁ : ∀ {k s} {A : Univ k} {B : Univ s} -> ⟦ A ⟧ -> A ⊎ B
inj₁ x = node $ 0 # (triv , x) , ([] , tt)

inj₂ : ∀ {k s} {A : Univ k} {B : Univ s} -> ⟦ B ⟧ -> A ⊎ B
inj₂ y = node $ 1 # (triv , y) , ([] , tt)

[_,_] : ∀ {k s π} {A : Univ k} {B : Univ s} {P : A ⊎ B -> Set π}
      -> ((x : ⟦ A ⟧) -> P (inj₁ x)) -> ((y : ⟦ B ⟧) -> P (inj₂ y)) -> ∀ s -> P s
[ f , g ] (node        (here ((, x) , ([] , _))))  = f x
[ f , g ] (node (there (here ((, y) , ([] , _))))) = g y
[ f , g ] (node (there (there ())))
