module OTT.Function.Elim where

open import OTT.Main
open import OTT.Function.Pi

ElimBy : ∀ {i b} {β : Level b} {I : Type i} {B}
       -> ((D : Desc I β) -> ⟦ D ⟧ᵈ B -> Set)
       -> (D : Desc I β)
       -> (∀ {j} -> Extend D B j -> B j)
       -> Set
ElimBy C (var i) k = C (var i) (k (refl i))
ElimBy C (π A D) k = Pi A λ x -> ElimBy C (D x) (k ∘ _,_ x)
ElimBy C (D ⊛ E) k = ∀ {x} -> C D x -> ElimBy C E (k ∘ _,_ x)

Hyp : ∀ {i b} {β : Level b} {I : Type i} {B}
    -> (∀ {i} -> B i -> Set) -> (D : Desc I β) -> ⟦ D ⟧ᵈ B -> Set
Hyp C (var i)  y      = C y
Hyp C (π A D)  f      = ∀ x -> Hyp C (D x) (f x) 
Hyp C (D ⊛ E) (x , y) = Hyp C D x × Hyp C E y

module _ {i b c} {β : Level b} {γ : Level c} {I : Type i} {D₀ : Desc I β}
         (P : ∀ {j} -> μ D₀ j -> Univ γ) (h : ElimBy (Hyp ⟦ P ⟧ᵒ) D₀ node) where
  mutual
    elimExtend : ∀ {j}
               -> (D : Desc I β)
               -> (k : ∀ {j} -> Extend D (μ D₀) j -> μ D₀ j)
               -> ElimBy (Hyp ⟦ P ⟧ᵒ) D k
               -> (e : Extend D (μ D₀) j)
               -> ⟦ P (k e) ⟧
    elimExtend (var i) k z  q      = J (λ j -> P ∘ k {j}) z q
    elimExtend (π A D) k h (x , e) = elimExtend (D x) (k ∘ _,_ x) (apply h x)   e
    elimExtend (D ⊛ E) k h (d , e) = elimExtend  E    (k ∘ _,_ d) (h (hyp D d)) e

    hyp : ∀ D -> (d : ⟦ D ⟧ᵈ (μ D₀)) -> Hyp ⟦ P ⟧ᵒ D d
    hyp (var i)  d      = elim d
    hyp (π A D)  f      = λ x -> hyp (D x) (f x)
    hyp (D ⊛ E) (x , y) = hyp D x , hyp E y

    elim : ∀ {j} -> (d : μ D₀ j) -> ⟦ P d ⟧
    elim (node e) = elimExtend D₀ node h e

private
  module Test where
    vec : ∀ {a} -> Type a -> ℕ -> Type a
    vec A = icmu
          $ var 0
          ∷ (π nat λ n -> A ⇨ var n ⊛ var (suc n))
          ∷ []

    Vec : ∀ {a} -> Type a -> ℕ -> Set
    Vec A n = ⟦ vec A n ⟧

    pattern vnilₑ      q      = #₀ q
    pattern vconsₑ {n} q x xs = !#₁ (n , x , xs , q)

    []ᵥ : ∀ {a} {A : Type a} -> Vec A 0
    []ᵥ = vnilₑ (refl 0)

    _∷ᵥ_ : ∀ {n a} {A : Type a} -> ⟦ A ⇒ vec A n ⇒ vec A (suc n) ⟧
    _∷ᵥ_ {n} = vconsₑ (refl (suc n))

    elimVec : ∀ {n a p} {π : Level p} {A : Type a}
            -> (P : ∀ {n} -> Vec A n -> Univ π)
            -> (∀ {n} {xs : Vec A n} -> (x : ⟦ A ⟧) -> ⟦ P xs ⇒ P (x ∷ᵥ xs) ⟧)
            -> ⟦ P []ᵥ ⟧
            -> (xs : Vec A n)
            -> ⟦ P xs ⟧
    elimVec P f z = elim P (z , lam λ x {_} r -> f x r)
