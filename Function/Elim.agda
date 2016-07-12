module OTT.Function.Elim where

open import OTT.Core
open import OTT.Coerce

Hyp : ∀ {i b γ} {ι : Level i} {β : Level b} {I : Type ι} {B}
    -> (∀ {i} -> B i -> Set γ) -> (D : Desc I β) -> ⟦ D ⟧ᵈ B -> Set γ
Hyp C (var i)  y      = C y
Hyp C (π A D)  f      = ∀ x -> Hyp C (D x) (f x) 
Hyp C (D ⊛ E) (x , y) = Hyp C D x × Hyp C E y

GElim : ∀ {i b γ} {ι : Level i} {β : Level b} {I : Type ι} {B}
      -> (∀ {i} -> B i -> Set γ) -> (D : Desc I β) -> (∀ {j} -> Extend D B j -> B j) -> Set γ
GElim C (var i) k = ∀ j -> (q : ⟦ i ≅ j ⟧) -> C (k q)
GElim C (π A D) k = ∀ x -> GElim C (D x) (k ∘ _,_ x)
GElim C (D ⊛ E) k = ∀ x -> Hyp C D x -> GElim C E (k ∘ _,_ x)

module _ {i b γ} {ι : Level i} {β : Level b} {I : Type ι} {D : Desc I β}
         (C : ∀ {j} -> μ D j -> Set γ) (h : GElim C D node) where
  mutual
    elimExtend : ∀ {j}
               -> (E : Desc I β) {k : ∀ {j} -> Extend E (μ D) j -> μ D j}
               -> GElim C E k
               -> (e : Extend E (μ D) j)
               -> C (k e)
    elimExtend (var i) z  q      = z _ q
    elimExtend (π A D) h (x , e) = elimExtend (D x) (h x)           e
    elimExtend (D ⊛ E) h (r , e) = elimExtend  E    (h r (hyp D r)) e

    hyp : ∀ E -> (d : ⟦ E ⟧ᵈ (μ D)) -> Hyp C E d
    hyp (var i)  d      = gelim d
    hyp (π A D)  f      = λ x -> hyp (D x) (f x)
    hyp (D ⊛ E) (r , s) = hyp D r , hyp E s

    gelim : ∀ {j} -> (d : μ D j) -> C d
    gelim (node e) = elimExtend D h e

Elim : ∀ {i b γ} {ι : Level i} {β : Level b} {I : Type ι} {B}
     -> (∀ {i} -> B i -> Set γ) -> (D : Desc I β) -> (∀ {j} -> Extend D B j -> B j) -> Set γ
Elim C (var i) k = C (k (refl i))
Elim C (π A D) k = ∀ x -> Elim C (D x) (k ∘ _,_ x)
Elim C (D ⊛ E) k = ∀ x -> Hyp C D x -> Elim C E (k ∘ _,_ x)

embedElim : ∀ {i b c} {ι : Level i} {β : Level b} {γ : Level c} {I : Type ι}
              {B : ⟦ I ⟧ -> Univ β} {C : ∀ {i} -> ⟦ B i ⟧ -> Univ γ}
          -> (D : Desc I β) {k : ∀ {j} -> Extend D ⟦ B ⟧ⁱ j -> ⟦ B j ⟧}
          -> Elim  ⟦ C ⟧ⁱ D k
          -> GElim ⟦ C ⟧ⁱ D k
embedElim {C = C} (var i) {k} z = λ j q -> J (λ j -> C ∘ k {j}) z q
embedElim         (π A D)     h = λ x -> embedElim (D x) (h x)
embedElim         (D ⊛ E)     h = λ x f -> embedElim E (h x f)

elim : ∀ {i b c} {ι : Level i} {β : Level b} {γ : Level c} {I : Type ι} {D : Desc I β} {j}
     -> (C : ∀ {j} -> μ D j -> Univ γ) -> (h : Elim ⟦ C ⟧ⁱ D node) -> (d : μ D j) -> ⟦ C d ⟧
elim {D = D} C h = gelim ⟦ C ⟧ⁱ (embedElim D h)

embedElim′ : ∀ {b γ} {β : Level b} {B} {C : B -> Set γ}
           -> (D : Desc unit β) {k : ∀ {j} -> Extend D (const B) j -> B}
           -> Elim  C D k
           -> GElim C D k
embedElim′ (var i) z = λ j q -> z
embedElim′ (π A D) h = λ x -> embedElim′ (D x) (h x)
embedElim′ (D ⊛ E) h = λ x f -> embedElim′ E (h x f)

elim′ : ∀ {b γ} {β : Level b} {D : Desc unit β} {j}
      -> (C : μ D triv -> Set γ) -> (h : Elim C D node) -> (d : μ D j) -> C d
elim′ {D = D} C h = gelim C (embedElim′ D h)
