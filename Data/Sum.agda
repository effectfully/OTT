module OTT.Data.Sum where

open import OTT.Main

infixr 3 _⊕_ _⊎_

_⊕_ : ∀ {k s} -> Univ k -> Univ s -> Type
A ⊕ B = rose ((A ⇨ ret ([] , triv)) ∷ (B ⇨ ret ([] , triv)) ∷ []) triv

_⊎_ : ∀ {k s} -> Univ k -> Univ s -> Set
A ⊎ B = ⟦ A ⊕ B ⟧

inj₁ : ∀ {k s} {A : Univ k} {B : Univ s} -> ⟦ A ⟧ -> A ⊎ B
inj₁ x = #₀ (x , [] , tt)

inj₂ : ∀ {k s} {A : Univ k} {B : Univ s} -> ⟦ B ⟧ -> A ⊎ B
inj₂ y = #₁ (y , [] , tt)

[_,_] : ∀ {k s π} {A : Univ k} {B : Univ s} {P : A ⊎ B -> Set π}
      -> ((x : ⟦ A ⟧) -> P (inj₁ x)) -> ((y : ⟦ B ⟧) -> P (inj₂ y)) -> ∀ s -> P s
[ f , g ] (#₀ (x , [] , tt)) = f x
[ f , g ] (#₁ (y , [] , tt)) = g y
[ f , g ]  ⟨⟩₂

smap : ∀ {k₁ k₂ s₁ s₂} {A₁ : Univ k₁} {A₂ : Univ k₂} {B₁ : Univ s₁} {B₂ : Univ s₂}
     -> ⟦ (A₁ ⇒ A₂) ⇒ (B₁ ⇒ B₂) ⇒ A₁ ⊕ B₁ ⇒ A₂ ⊕ B₂ ⟧
smap f g = [ inj₁ ∘ f , inj₂ ∘ g ]
