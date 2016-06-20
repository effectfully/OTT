module OTT.Function.Elim where

open import OTT.Main
open import OTT.Function.Pi
open import OTT.Function.Erase

Hyp : ∀ {i b} {β : Level b} {I : Type i} {B}
    -> (∀ {i} -> B i -> Set) -> (D : Desc I β) -> ⟦ D ⟧ᵈ B -> Set
Hyp P (var i)  y      = P y
Hyp P (π A D)  f      = ∀ x -> Hyp P (D x) (f x) 
Hyp P (D ⊛ E) (x , y) = Hyp P D x × Hyp P E y

Elimₑ : ∀ {i b} {β : Level b} {I : Type i} {B}
      -> (∀ {i} -> B i -> Set) -> (D : Desc I β) -> (∀ {j} -> Extend D B j -> B j) -> Set
Elimₑ P (var i) k = ∀ {j} -> (q : ⟦ i ≅ j ⟧) -> P (k q)
Elimₑ P (π A D) k = Pi A λ x -> Elimₑ P (D x) (k ∘ _,_ x)
Elimₑ P (D ⊛ E) k = ∀ x -> Hyp P D x -> Elimₑ P E (k ∘ _,_ x)

module _ {i b} {β : Level b} {I : Type i} {D : Desc I β}
         (P : ∀ {j} -> μ D j -> Set) (h : Elimₑ P D node) where
  mutual
    elimExtend : ∀ {j}
               -> (E : Desc I β) {k : ∀ {j} -> Extend E (μ D) j -> μ D j}
               -> Elimₑ P E k
               -> (e : Extend E (μ D) j)
               -> P (k e)
    elimExtend (var i) z  q      = z q
    elimExtend (π A D) h (x , e) = elimExtend (D x) (apply h x)     e
    elimExtend (D ⊛ E) h (r , e) = elimExtend  E    (h r (hyp D r)) e

    hyp : ∀ E -> (d : ⟦ E ⟧ᵈ (μ D)) -> Hyp P E d
    hyp (var i)  d      = elimₑ d
    hyp (π A D)  f      = λ x -> hyp (D x) (f x)
    hyp (D ⊛ E) (r , s) = hyp D r , hyp E s

    elimₑ : ∀ {j} -> (d : μ D j) -> P d
    elimₑ (node e) = elimExtend D h e

Elim′ : ∀ {i b} {β : Level b} {I : Type i} {B}
      -> (B -> Set) -> (D : Desc I β) -> (Extend (Erase D) (λ _ -> B) triv -> B) -> Set
Elim′ P (var i) k = P (k tt)
Elim′ P (π A D) k = Pi A λ x -> Elim′ P (D x) (k ∘ _,_ x)
Elim′ P (D ⊛ E) k = ∀ x -> Hyp P (Erase D) x -> Elim′ P E (k ∘ _,_ x)

embedElim′ : ∀ {i b} {β : Level b} {I : Type i} {B} {P : B -> Set}
           -> (D : Desc I β) {k : Extend (Erase D) (λ _ -> B) triv -> B}
           -> Elim′ P  D        k
           -> Elimₑ P (Erase D) k
embedElim′ (var i) z = λ q -> z
embedElim′ (π A D) h = lam λ x -> embedElim′ (D x) (apply h x)
embedElim′ (D ⊛ E) h = λ x f -> embedElim′ E (h x f)

elim′ : ∀ {i b c} {I : Type i} {β : Level b} {γ : Level c} {D : Desc I β} {j}
      -> (P : μ (Erase D) triv -> Set) -> (h : Elim′ P D node) -> (d : μ D j) -> P (erase d)
elim′ {D = D} P h = elimₑ P (embedElim′ D h) ∘ erase

Elim : ∀ {i b} {β : Level b} {I : Type i} {B}
     -> (∀ {i} -> B i -> Set) -> (D : Desc I β) -> (∀ {j} -> Extend D B j -> B j) -> Set
Elim P (var i) k = P (k (refl i))
Elim P (π A D) k = Pi A λ x -> Elim P (D x) (k ∘ _,_ x)
Elim P (D ⊛ E) k = ∀ x -> Hyp P D x -> Elim P E (k ∘ _,_ x)

embedElim : ∀ {i b p} {β : Level b} {π : Level p} {I : Type i}
              {B : ⟦ I ⟧ -> Univ β} {P : ∀ {i} -> ⟦ B i ⟧ -> Univ π}
          -> (D : Desc I β) {k : ∀ {j} -> Extend D ⟦ B ⟧ᵒ j -> ⟦ B j ⟧}
          -> Elim  ⟦ P ⟧ᵒ D k
          -> Elimₑ ⟦ P ⟧ᵒ D k
embedElim {P = P} (var i) {k} z = λ q -> J (λ j -> P ∘ k {j}) z q
embedElim         (π A D)     f = lam λ x -> embedElim (D x) (apply f x)
embedElim         (D ⊛ E)     f = λ x h -> embedElim E (f x h)

elim : ∀ {i b p} {β : Level b} {π : Level p} {I : Type i} {D : Desc I β} {j}
     -> (P : ∀ {j} -> μ D j -> Univ π) -> (h : Elim ⟦ P ⟧ᵒ D node) -> (d : μ D j) -> ⟦ P d ⟧
elim {D = D} P h = elimₑ ⟦ P ⟧ᵒ (embedElim D h)



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
    elimVec P f z = elim P (z , lam λ x xs -> f x)
