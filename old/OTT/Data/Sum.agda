module OTT.Data.Sum where

open import OTT.Main

infixr 3 _⊕_ _⊎_

_⊕_ : ∀ {k s} -> Univ k -> Univ s -> Type
A ⊕ B = rose ((A ⇨ ret ([] , triv)) ∷ (B ⇨ ret ([] , triv)) ∷ []) triv

_⊎_ : ∀ {k s} -> Univ k -> Univ s -> Set
A ⊎ B = ⟦ A ⊕ B ⟧

pattern inj₁ x = #₀ (x , [] , tt)
pattern inj₂ y = #₁ (y , [] , tt)

[_,_] : ∀ {k s π} {A : Univ k} {B : Univ s} {P : A ⊎ B -> Set π}
      -> (∀ x -> P (inj₁ x)) -> (∀ y -> P (inj₂ y)) -> ∀ s -> P s
[ f , g ] (inj₁ x) = f x
[ f , g ] (inj₂ y) = g y
[ f , g ]  ⟨⟩₂

smap : ∀ {k₁ k₂ s₁ s₂} {A₁ : Univ k₁} {A₂ : Univ k₂} {B₁ : Univ s₁} {B₂ : Univ s₂}
     -> ⟦ (A₁ ⇒ A₂) ⇒ (B₁ ⇒ B₂) ⇒ A₁ ⊕ B₁ ⇒ A₂ ⊕ B₂ ⟧
smap f g = [ inj₁ ∘ f , inj₂ ∘ g ]
