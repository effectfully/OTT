module OTT.Property.Eq where

import Data.Nat.Base as Nat

open import OTT.Main
open import OTT.Function.Pi

infix 4 _≟_

module _ where
  open import Relation.Binary.PropositionalEquality.TrustMe

  contr : {A : Prop} {x y : ⟦ A ⟧} -> x ≡ y
  contr = trustMe

SemEq : ∀ {i a} {ι : Level i} {α : Level a} {I : Type ι} -> Desc I α -> Set
SemEq (var i) = ⊤
SemEq (π A D) = ⊥
SemEq (D ⊛ E) = SemEq D × SemEq E

mutual
  ExtendEq : ∀ {i a} {ι : Level i} {α : Level a} {I : Type ι} -> Desc I α -> Set
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
  decSem : ∀ {i a} {ι : Level i} {α : Level a}
             {I : Type ι} {D₀ : Desc I α} {{eqD₀ : ExtendEq D₀}}
         -> (D : Desc I α) {{eqD : SemEq D}} -> IsSet (⟦ D ⟧ᵈ (μ D₀))
  decSem (var i)                d₁        d₂       = decMu d₁ d₂
  decSem (π A D) {{()}}
  decSem (D ⊛ E) {{eqD , eqE}} (s₁ , t₁) (s₂ , t₂) =
    decSem D {{eqD}} s₁ s₂ <,>ᵈ decSem E {{eqE}} t₁ t₂

  decExtend : ∀ {i a} {ι : Level i} {α : Level a} {I : Type ι}
                {D₀ : Desc I α} {j} {{eqD₀ : ExtendEq D₀}}
            -> (D : Desc I α) {{eqD : ExtendEq D}} -> IsSet (Extend D (μ D₀) j)
  decExtend (var i)                q₁        q₂       = yes contr
  decExtend (π A D) {{eqA , eqD}} (x₁ , e₁) (x₂ , e₂) =
    _≟_ {{eqA}} x₁ x₂ <,>ᵈⁱ decExtend (D x₁) {{apply eqD x₁}} e₁
  decExtend (D ⊛ E) {{eqD , eqE}} (s₁ , e₁) (s₂ , e₂) =
    decSem D {{eqD}} s₁ s₂ <,>ᵈ decExtend E {{eqE}} e₁ e₂

  decMu : ∀ {i a} {ι : Level i} {α : Level a} {I : Type ι}
            {D : Desc I α} {j} {{eqD : ExtendEq D}}
        -> IsSet (μ D j)
  decMu {D = D} (node e₁) (node e₂) = dcong node node-inj (decExtend D e₁ e₂)

  _≟_ : ∀ {a} {α : Level a} {A : Univ α} {{eqA : Eq A}} -> IsSet ⟦ A ⟧
  _≟_ {A = bot     }                ()        ()
  _≟_ {A = top     }                tt        tt       = yes prefl
  _≟_ {A = nat     }                n₁        n₂       = n₁ Nat.≟ n₂
  _≟_ {A = enum n  }               (tag e₁)  (tag e₂)  = dcong tag tag-inj (decEnum n e₁ e₂)
  _≟_ {A = univ α  } {{()}}
  _≟_ {A = σ A B   } {{eqA , eqB}} (x₁ , y₁) (x₂ , y₂) =
    _≟_ {{eqA}} x₁ x₂ <,>ᵈⁱ _≟_ {{apply eqB x₁}} y₁
  _≟_ {A = π A B   } {{()}}
  _≟_ {A = desc I α} {{()}}
  _≟_ {A = imu D j }                d₁        d₂       = decMu d₁ d₂

coerceFamEnum : ∀ {n} {e f : Apply Enum n} -> (A : Apply Enum n -> Set) -> ⟦ e ≅ f ⟧ -> A e -> A f
coerceFamEnum {0}           {tag ()      } {tag ()      } A q  x
coerceFamEnum {1}           {tag tt      } {tag tt      } A q  x = x
coerceFamEnum {suc (suc n)} {tag nothing } {tag nothing } A q  x = x
coerceFamEnum {suc (suc n)} {tag (just _)} {tag (just _)} A q  x =
  coerceFamEnum (A ∘ tag ∘ just ∘ detag) q x
coerceFamEnum {suc (suc n)} {tag nothing } {tag (just _)} A () x
coerceFamEnum {suc (suc n)} {tag (just _)} {tag nothing } A () x

mutual
  observeSem : ∀ {i a} {ι : Level i} {α : Level a}
                 {I : Type ι} {E : Desc I α} {{eqE : ExtendEq E}}
             -> (D : Desc I α) {{edD : SemEq D}}
             -> (d₁ d₂ : ⟦ D ⟧ᵈ (μ E)) -> ⟦ D , d₁ ≅s D , d₂ ⟧ -> d₁ ≡ d₂
  observeSem (var i)                d₁        d₂        q        = observe q
  observeSem (π A D) {{()}}         d₁        d₂        q
  observeSem (D ⊛ E) {{eqD , eqE}} (d₁ , e₁) (d₂ , e₂) (qd , qe) =
    pcong₂ _,_ (observeSem D {{eqD}} d₁ d₂ qd) (observeSem E {{eqE}} e₁ e₂ qe)

  observeExtend : ∀ {i a} {ι : Level i} {α : Level a} {I : Type ι}
                    {E : Desc I α} {j} {{edE : ExtendEq E}}
                -> (D : Desc I α) {{edD : ExtendEq D}}
                -> (e₁ e₂ : Extend D (μ E) j) -> ⟦ D , e₁ ≅e D , e₂ ⟧ -> e₁ ≡ e₂
  observeExtend (var i)                q₁        q₂        q        = contr
  observeExtend (π A D) {{eqA , eqD}} (x₁ , e₁) (x₂ , e₂) (qx , qe)
    rewrite observe {x = x₁} {x₂} {{eqA}} qx =
      pcong (_,_ _) (observeExtend (D x₂) {{apply eqD x₂}} e₁ e₂ qe)
  observeExtend (D ⊛ E) {{eqD , eqE}} (d₁ , e₁) (d₂ , e₂) (qd , qe) =
    pcong₂ _,_ (observeSem D {{eqD}} d₁ d₂ qd) (observeExtend E {{eqE}} e₁ e₂ qe)

  observeMu : ∀ {i a} {ι : Level i} {α : Level a} {I : Type ι} {j}
                {D : Desc I α} {d e : μ D j} {{eqD : ExtendEq D}}
            -> ⟦ d ≅ e ⟧ -> d ≡ e
  observeMu {D = D} {node e₁} {node e₂} q = pcong node (observeExtend D e₁ e₂ q)

  observe : ∀ {a} {α : Level a} {A : Univ α} {x y : ⟦ A ⟧} {{eqA : Eq A}} -> ⟦ x ≅ y ⟧ -> x ≡ y
  observe {A = bot     } {()}      {()}
  observe {A = top     }                                    q        = prefl
  observe {A = nat     }                                    q        = coerceFamℕ    (_ ≡_) q prefl
  observe {A = enum n  } {e₁}      {e₂}                     q        = coerceFamEnum (_ ≡_) q prefl
  observe {A = univ α  }                     {{()}}
  observe {A = σ A B   } {x₁ , y₁} {x₂ , y₂} {{eqA , eqB}} (qx , qy)
    rewrite observe {x = x₁} {x₂} {{eqA}} qx = pcong (_,_ _) (observe {{apply eqB x₂}} qy)
  observe {A = π A B   }                     {{()}}
  observe {A = desc I α}                     {{()}}
  observe {A = imu D j } {node e₁} {node e₂}                q        = observeMu q

module _ where
  open import Relation.Binary.PropositionalEquality.TrustMe

  eobserve : ∀ {a} {α : Level a} {A : Univ α} {x y : ⟦ A ⟧} {{eqA : Eq A}} -> ⟦ x ≅ y ⟧ -> x ≡ y
  eobserve = erase ∘ observe

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
