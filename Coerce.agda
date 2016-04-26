{-# OPTIONS --no-termination-check #-}

module OTT.Coerce where

open import OTT.Prelude
open import OTT.Core

-- I'll probably fix this.
postulate noway : {A : Set} -> A

Coerce : ∀ {k₁ k₂} -> ⟦ k₁ ≟ᵇ k₂ ⟧ -> Univ k₁ -> Univ k₂
Coerce {false} {false} _  A = A
Coerce {true } {true } _  A = A
Coerce {false} {true } () A
Coerce {true } {false} () A

coerceℕFam : ∀ {n₁ n₂} -> (A : ℕ -> Set) -> ⟦ n₁ ≅ n₂ ⟧ -> A n₁ -> A n₂
coerceℕFam {0}      {0}      A q  x = x
coerceℕFam {suc n₁} {suc n₂} A q  x = coerceℕFam (A ∘ suc) q x
coerceℕFam {0}      {suc _}  A () x
coerceℕFam {suc _}  {0}      A () x

coerceFin : ∀ {n₁ n₂} -> ⟦ n₁ ≅ n₂ ⟧ -> Fin n₁ -> Fin n₂
coerceFin = coerceℕFam Fin

mutual
  coerce : ∀ {k s} {A : Univ k} {B : Univ s} -> ⟦ A ≈ B ⇒ A ⇒ B ⟧
  coerce {false} {false} (f , _) = f
  coerce {true } {true }  q      = coerce′ q
  coerce {false} {true }  ()
  coerce {true } {false}  ()

  coerce′ : ∀ {k s} {A : Univ k} {B : Univ s} -> ⟦ A ≃ B ⇒ A ⇒ B ⟧
  coerce′ {A = bot     } {bot     } q ()
  coerce′ {A = top     } {top     } q _  = _
  coerce′ {A = nat     } {nat     } q n  = n
  coerce′ {A = fin n₁  } {fin n₂  } q i  = coerceFin q i
  coerce′ {A = univ k₁ } {univ k₂ } q A  = Coerce q A
  coerce′ {A = σ A₁ B₁ } {σ A₂ B₂ } q p  = let q₁ , q₂ = q ; x , y = p in
    coerce q₁ x , coerce (q₂ x (coerce q₁ x) (coherence q₁ x)) y
  coerce′ {A = π A₁ B₁ } {π A₂ B₂ } q f  = let q₁ , q₂ = q in
    λ x -> coerce (q₂ (coerce q₁ x) x (coherence q₁ x)) (f (coerce q₁ x))
  coerce′ {A = mu D₁ i₁} {mu D₂ i₂} q d  = let qD , qi = q in coerceMu qD qi d
  coerce′ _ _ = noway

  coerceSem : ∀ {I₁ I₂} {F₁ : ⟦ I₁ ⟧ -> Type} {F₂ : ⟦ I₂ ⟧ -> Type}
            -> (D₁ : Desc I₁)
            -> (D₂ : Desc I₂)
            -> ⟦ D₁ ≅ D₂ ⟧
            -> ⟦ F₁ ≅ F₂ ⟧
            -> (⟦ D₁ ⟧ᴰ λ x₁ -> ⟦ F₁ x₁ ⟧)
            -> (⟦ D₂ ⟧ᴰ λ x₂ -> ⟦ F₂ x₂ ⟧)
  coerceSem (var j₁)  (var j₂)   qj       qF  x      = coerce (qF j₁ j₂ qj) x
  coerceSem (π A₁ B₁) (π A₂ B₂) (qA , qB) qF  f      = λ x ->
    let qA′ = sym A₁ {A₂} qA
        x′  = coerce qA′ x
    in coerceSem (B₁ x′) (B₂ x) (qB x′ x (sym x (coherence qA′ x))) qF (f x′)
  coerceSem (D₁ ⊛ E₁) (D₂ ⊛ E₂) (qD , qE) qF (s , t) =
    coerceSem D₁ D₂ qD qF s , coerceSem E₁ E₂ qE qF t
  coerceSem _ _ qD qF e = noway

  coerceExtend : ∀ {I₁ I₂} {F₁ : ⟦ I₁ ⟧ -> Type} {F₂ : ⟦ I₂ ⟧ -> Type} {i₁ i₂}
               -> (D₁ : Desc I₁)
               -> (D₂ : Desc I₂)
               -> ⟦ D₁ ≅ D₂ ⟧
               -> ⟦ F₁ ≅ F₂ ⟧
               -> ⟦ i₁ ≅ i₂ ⟧
               -> Extend D₁ (λ x₁ -> ⟦ F₁ x₁ ⟧) i₁
               -> Extend D₂ (λ x₂ -> ⟦ F₂ x₂ ⟧) i₂
  coerceExtend (var j₁)  (var j₂)   qj       qF qi  qji    = trans j₂ (right j₁ qj qji) qi
  coerceExtend (π A₁ B₁) (π A₂ B₂) (qA , qB) qF qi (x , e) = let x′ = coerce qA x in
    x′ , coerceExtend (B₁ x) (B₂ x′) (qB x x′ (coherence qA x)) qF qi e
  coerceExtend (D₁ ⊛ E₁) (D₂ ⊛ E₂) (qD , qE) qF qi (s , e) =
    coerceSem D₁ D₂ qD qF s , coerceExtend E₁ E₂ qE qF qi e
  coerceExtend _ _ qD qF qi e = noway

  coerceMu : ∀ {I₁ I₂} {D₁ : Desc I₁} {D₂ : Desc I₂} {i₁ i₂}
           -> ⟦ D₁ ≅ D₂ ⟧ -> ⟦ i₁ ≅ i₂ ⟧ -> μ D₁ i₁ -> μ D₂ i₂
  coerceMu {D₁ = D₁} {D₂} qD qi (node d₁) = node (coerceExtend D₁ D₂ qD (λ _ _ qj -> qD , qj) qi d₁)

  postulate
    refl      : ∀ {k} {A : Univ k} -> (x : ⟦ A ⟧) -> ⟦ x ≅ x ⟧
    coherence : ∀ {k s} {A : Univ k} {B : Univ s}
              -> (q : ⟦ A ≈ B ⟧) -> (x : ⟦ A ⟧) -> ⟦ x ≅ coerce q x ⟧
    cong-≅z   : ∀ {k s t} {A : Univ k} {B : Univ s} {C : Univ t}
              -> (x : ⟦ A ⟧) {y : ⟦ B ⟧} {z : ⟦ C ⟧} -> (q : ⟦ x ≅ y ⟧) -> ⟦ (x ≅ z) ≈ (y ≅ z)⟧
    huip      : ∀ {k s} {A : Univ k} {B : Univ s}
              -> (x : ⟦ A ⟧) {y : ⟦ B ⟧} -> (q : ⟦ x ≅ y ⟧) -> ⟦ refl x ≅ q ⟧

  right : ∀ {k s t} {A : Univ k} {B : Univ s} {C : Univ t}
        -> (x : ⟦ A ⟧) {y : ⟦ B ⟧} {z : ⟦ C ⟧} -> ⟦ x ≅ y ⟧ -> ⟦ x ≅ z ⟧ -> ⟦ y ≅ z ⟧
  right x q₁ = proj₁ (cong-≅z x q₁)

  trans : ∀ {k s t} {A : Univ k} {B : Univ s} {C : Univ t}
        -> (x : ⟦ A ⟧) {y : ⟦ B ⟧} {z : ⟦ C ⟧} -> ⟦ x ≅ y ⟧ -> ⟦ y ≅ z ⟧ -> ⟦ x ≅ z ⟧
  trans x {y} q₁ = proj₂ (cong-≅z x q₁)

  sym : ∀ {k s} {A : Univ k} {B : Univ s}
      -> (x : ⟦ A ⟧) {y : ⟦ B ⟧} -> ⟦ x ≅ y ⟧ -> ⟦ y ≅ x ⟧
  sym x q = right x q (refl x)

  left : ∀ {k s t} {A : Univ k} {B : Univ s} {C : Univ t}
       -> (x : ⟦ A ⟧) {y : ⟦ B ⟧} {z : ⟦ C ⟧} -> ⟦ x ≅ y ⟧ -> ⟦ z ≅ y ⟧ -> ⟦ x ≅ z ⟧
  left x {z = z} q₁ q₂ = trans x q₁ (sym z q₂)

subst : ∀ {k s} {A : Univ k} {x y} -> (P : ⟦ A ⟧ -> Univ s) -> ⟦ x ≅ y ⇒ P x ⇒ P y ⟧
subst P q = coerce (refl P _ _ q)

subst₂ : ∀ {k s t} {A : Univ k} {B : ⟦ A ⟧ -> Univ s} {i j} {x : ⟦ B i ⟧} {y : ⟦ B j ⟧}
       -> (P : ∀ x -> ⟦ B x ⟧ -> Univ t) -> ⟦ i ≅ j ⇒ x ≅ y ⇒ P i x ⇒ P j y ⟧
subst₂ P q₁ q₂ = coerce (refl P _ _ q₁ _ _ q₂)

J : ∀ {k s} {A : Univ k} {x y : ⟦ A ⟧}
  -> (P : (y : ⟦ A ⟧) -> ⟦ x ≅ y ⟧ -> Univ s)
  -> ⟦ P _ (refl x) ⟧
  -> (q : ⟦ x ≅ y ⟧)
  -> ⟦ P _ q ⟧
J {x = x} P z q = subst₂ P q (huip x q) z
