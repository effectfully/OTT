-- We can do slightly better by adding something like
-- `eqable : ∀ {a} {α : Level a} -> (A : Univ α) -> Maybe (Eq A)`

module OTT.Property.Eq where

import Data.Nat.Base as Nat

open import OTT.Main
open import OTT.Function.Pi

infix 4 _≟_

-- TODO?
module _ where
  open import Relation.Binary.PropositionalEquality.TrustMe

  contr : {A : Prop} {x y : ⟦ A ⟧} -> x ≡ y
  contr = trustMe

-- We could compare functions with a finite domain for equality,
-- but then equality can't be `_≡_`.
SemEq : ∀ {i a} {α : Level a} {I : Type i} -> Desc I α -> Set
SemEq (var i) = ⊤
SemEq (π A D) = ⊥
SemEq (D ⊛ E) = SemEq D × SemEq E

mutual
  ExtendEq : ∀ {i a} {α : Level a} {I : Type i} -> Desc I α -> Set
  ExtendEq (var i) = ⊤
  ExtendEq (π A D) = Eq A × Pi A λ x -> ExtendEq (D x)
  ExtendEq (D ⊛ E) = SemEq D × ExtendEq E

  Eq : ∀ {a} {α : Level a} -> Univ α -> Set
  Eq  bot       = ⊤
  Eq  top       = ⊤
  Eq  nat       = ⊤
  Eq (enum n)   = ⊤
  Eq (σ A B)    = Eq A × Pi A λ x -> Eq (B x)
  Eq (imu D j)  = ExtendEq D
  Eq  _         = ⊥

mutual
  decSem : ∀ {i a} {α : Level a} {I : Type i} {D₀ : Desc I α} {{eqD₀ : ExtendEq D₀}}
         -> (D : Desc I α) {{eqD : SemEq D}} -> IsSet (⟦ D ⟧ᵈ (μ D₀))
  decSem (var i)                d₁        d₂       = decMu d₁ d₂
  decSem (π A D) {{()}}
  decSem (D ⊛ E) {{eqD , eqE}} (s₁ , t₁) (s₂ , t₂) =
    decSem D {{eqD}} s₁ s₂ <,>ᵈ decSem E {{eqE}} t₁ t₂

  decExtend : ∀ {i a} {α : Level a} {I : Type i} {j} {D₀ : Desc I α} {{eqD₀ : ExtendEq D₀}}
            -> (D : Desc I α) {{eqD : ExtendEq D}} -> IsSet (Extend D (μ D₀) j)
  decExtend (var i)                q₁        q₂       = yes contr
  decExtend (π A D) {{eqA , eqD}} (x₁ , e₁) (x₂ , e₂) =
    _≟_ {{eqA}} x₁ x₂ <,>ᵈᵒ decExtend (D x₁) {{apply eqD x₁}} e₁
  decExtend (D ⊛ E) {{eqD , eqE}} (s₁ , e₁) (s₂ , e₂) =
    decSem D {{eqD}} s₁ s₂ <,>ᵈ decExtend E {{eqE}} e₁ e₂

  decMu : ∀ {i a} {α : Level a} {I : Type i} {D : Desc I α} {j} {{eqD : ExtendEq D}}
        -> IsSet (μ D j)
  decMu {D = D} (node e₁) (node e₂) = dcong node node-inj (decExtend D e₁ e₂)

  _≟_ : ∀ {a} {α : Level a} {A : Univ α} {{eqA : Eq A}} -> IsSet ⟦ A ⟧
  _≟_ {A = bot     }                ()        ()
  _≟_ {A = top     }                tt        tt       = yes prefl
  _≟_ {A = α ≡ˢˡ β } {{()}}
  _≟_ {A = nat     }                n₁        n₂       = n₁ Nat.≟ n₂
  _≟_ {A = enum n  }               (tag e₁)  (tag e₂)  = dcong tag tag-inj (decEnum n e₁ e₂)
  _≟_ {A = univ α  } {{()}}
  _≟_ {A = σ A B   } {{eqA , eqB}} (x₁ , y₁) (x₂ , y₂) =
    _≟_ {{eqA}} x₁ x₂ <,>ᵈᵒ _≟_ {{apply eqB x₁}} y₁
  _≟_ {A = π A B   } {{()}}
  _≟_ {A = desc I α} {{()}}
  _≟_ {A = imu D j }                d₁        d₂       = decMu d₁ d₂

private
  module Test where
    open import OTT.Data.Fin
    open import OTT.Data.Sum

    ns₁ : List (list nat ⊕ σ nat fin)
    ns₁ = inj₁ (1 ∷ 4 ∷ []) ∷ inj₂ (3 , fsuc fzero) ∷ inj₂ (2 , fzero) ∷ []

    ns₂ : List (list nat ⊕ σ nat fin)
    ns₂ = inj₁ (1 ∷ 4 ∷ []) ∷ inj₂ (2 , fsuc fzero) ∷ inj₂ (2 , fzero) ∷ []

    ns₃ : List (list nat ⊕ σ nat fin)
    ns₃ = inj₁ (1 ∷ 4 ∷ []) ∷ inj₂ (3 , fsuc fzero) ∷ []

    test₁ : (ns₁ ≟ ns₁) ≡ yes prefl
    test₁ = prefl

    test₂ : (ns₁ ≟ ns₂) ≡ no _
    test₂ = prefl

    test₃ : (ns₁ ≟ ns₃) ≡ no _
    test₃ = prefl
