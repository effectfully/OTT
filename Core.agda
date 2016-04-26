{-# OPTIONS --no-positivity-check --no-termination-check #-}

module OTT.Core where

open import OTT.Prelude

infixr 1 _&_
infixr 2 _⇒_ _⇨_
infix  3 _≈_ _≃_ _≅_ _≅d_ _≅s_ _≅e_
infixr 6 _⊛_

Unit = Fin 1

tr : Unit
tr = fzero

data Univ : Bool -> Set

Prop = Univ false
Type = Univ true

⟦_⟧ : ∀ {k} -> Univ k -> Set

_≈_  : ∀ {k s} -> Univ k -> Univ s -> Prop
_≃_  : ∀ {k s} -> Univ k -> Univ s -> Prop
_≅_  : ∀ {k s} {A : Univ k} {B : Univ s} -> ⟦ A ⟧ -> ⟦ B ⟧ -> Prop

data Desc (I : Type) : Set where
  var : ⟦ I ⟧ -> Desc I
  π   : ∀ {k} -> (A : Univ k) -> (⟦ A ⟧ -> Desc I) -> Desc I
  _⊛_ : Desc I -> Desc I -> Desc I

_⇨_ : ∀ {k I} -> Univ k -> Desc I -> Desc I
A ⇨ D = π A λ _ -> D

⟦_⟧ᴰ : ∀ {I} -> Desc I -> (⟦ I ⟧ -> Set) -> Set
⟦ var i ⟧ᴰ F = F i
⟦ π A B ⟧ᴰ F = ∀ x -> ⟦ B x ⟧ᴰ F
⟦ D ⊛ E ⟧ᴰ F = ⟦ D ⟧ᴰ F × ⟦ E ⟧ᴰ F

Extend : ∀ {I} -> Desc I -> (⟦ I ⟧ -> Set) -> ⟦ I ⟧ -> Set
Extend (var j) F i = ⟦ j ≅ i ⟧
Extend (π A B) F i = ∃ λ x -> Extend (B x) F i
Extend (D ⊛ E) F i = ⟦ D ⟧ᴰ F × Extend E F i

record μ {I} (D : Desc I) i : Set where
  inductive
  constructor node
  field knot : Extend D (μ D) i

data Univ where
  bot  : Prop
  top  : Prop
  nat  : Type
  fin  : ℕ -> Type
  univ : Bool -> Type
  σ    : ∀ {k s} -> (A : Univ k) -> (⟦ A ⟧ -> Univ s) -> Univ (k ∨ s)
  π    : ∀ {k s} -> (A : Univ k) -> (⟦ A ⟧ -> Univ s) -> Univ  s
  desc : Type -> Type
  mu   : ∀ {I} -> Desc I -> ⟦ I ⟧ -> Type

⟦ bot    ⟧ = ⊥
⟦ top    ⟧ = ⊤
⟦ nat    ⟧ = ℕ
⟦ fin n  ⟧ = Fin n
⟦ univ k ⟧ = Univ k
⟦ σ A B  ⟧ = ∃ λ x -> ⟦ B x ⟧
⟦ π A B  ⟧ = ∀   x -> ⟦ B x ⟧
⟦ desc I ⟧ = Desc I
⟦ mu D i ⟧ = μ D i

prop = univ false
type = univ true

_&_ : ∀ {k s} -> Univ k -> Univ s -> Univ (k ∨ s)
A & B = σ A λ _ -> B

_⇒_ : ∀ {k s} -> Univ k -> Univ s -> Univ  s
A ⇒ B = π A λ _ -> B

_≟ᵇ_ : Bool -> Bool -> Prop
false ≟ᵇ false = top
true  ≟ᵇ true  = top
_     ≟ᵇ _     = bot

_≟ⁿ_ : ℕ -> ℕ -> Prop
0     ≟ⁿ 0     = top
suc n ≟ⁿ suc m = n ≟ⁿ m
_     ≟ⁿ _     = bot

_≟ᶠ_ : ∀ {n m} -> Fin n -> Fin m -> Prop
fzero  ≟ᶠ fzero  = top
fsuc i ≟ᶠ fsuc j = i ≟ᶠ j
_      ≟ᶠ _      = bot

_≅d_ : ∀ {I₁ I₂} -> Desc I₁ -> Desc I₂ -> Prop
var i₁  ≅d var i₂  = i₁ ≅ i₂
π A₁ B₁ ≅d π A₂ B₂ = A₁ ≈ A₂ & B₁ ≅ B₂
D₁ ⊛ E₁ ≅d D₂ ⊛ E₂ = D₁ ≅d D₂ & E₁ ≅d E₂
_       ≅d _       = bot

_≈_ {false} {false} A₁ A₂ = A₁ ⇒ A₂ & A₂ ⇒ A₁
_≈_ {true } {true } A₁ A₂ = A₁ ≃ A₂
_≈_                 _  _  = bot

bot      ≃ bot      = top
top      ≃ top      = top
nat      ≃ nat      = top
fin n₁   ≃ fin n₂   = n₁ ≟ⁿ n₂
univ k₁  ≃ univ k₂  = k₁ ≟ᵇ k₂
σ A₁ B₁  ≃ σ A₂ B₂  = A₁ ≈ A₂ & B₁ ≅ B₂
π A₁ B₁  ≃ π A₂ B₂  = A₂ ≈ A₁ & π A₁ λ x₁ -> π A₂ λ x₂ -> x₂ ≅ x₁ ⇒ B₁ x₁ ≈ B₂ x₂
desc I₁  ≃ desc I₂  = I₁ ≃ I₂
mu D₁ i₁ ≃ mu D₂ i₂ = D₁ ≅d D₂ & i₁ ≅ i₂
_        ≃ _        = bot

_≅e_ : ∀ {I₁ I₂} {F₁ : ⟦ I₁ ⟧ -> Type} {F₂ : ⟦ I₂ ⟧ -> Type} {i₁ i₂}
     -> (∃ λ D₁ -> Extend D₁ (λ x₁ -> ⟦ F₁ x₁ ⟧) i₁)
     -> (∃ λ D₂ -> Extend D₂ (λ x₂ -> ⟦ F₂ x₂ ⟧) i₂)
     -> Prop

_≅_ {A = bot     } {bot     } _  _  = top
_≅_ {A = top     } {top     } _  _  = top
_≅_ {A = nat     } {nat     } n₁ n₂ = n₁ ≟ⁿ n₂
_≅_ {A = fin n₁  } {fin n₂  } i₁ i₂ = i₁ ≟ᶠ i₂
_≅_ {A = univ k₁ } {univ k₂ } A₁ A₂ = A₁ ≈ A₂
_≅_ {A = σ A₁ B₁ } {σ A₂ B₂ } p₁ p₂ = let x₁ , y₁ = p₁ ; x₂ , y₂ = p₂ in x₁ ≅ x₂ & y₁ ≅ y₂
_≅_ {A = π A₁ B₁ } {π A₂ B₂ } f₁ f₂ = π A₁ λ x₁ -> π A₂ λ x₂ -> x₁ ≅ x₂ ⇒ f₁ x₁ ≅ f₂ x₂
_≅_ {A = desc I₁ } {desc I₂ } D₁ D₂ = D₁ ≅d D₂
_≅_ {A = mu D₁ i₁} {mu D₂ i₂} d₁ d₂ = let node e₁ = d₁; node e₂ = d₂ in D₁ , e₁ ≅e D₂ , e₂
_≅_                           _  _  = bot

_≅s_ : ∀ {I₁ I₂} {F₁ : ⟦ I₁ ⟧ -> Type} {F₂ : ⟦ I₂ ⟧ -> Type}
     -> (∃ λ D₁ -> ⟦ D₁ ⟧ᴰ λ x₁ -> ⟦ F₁ x₁ ⟧)
     -> (∃ λ D₂ -> ⟦ D₂ ⟧ᴰ λ x₂ -> ⟦ F₂ x₂ ⟧)
     -> Prop
var i₁  , x₁      ≅s var i₂  , x₂      = x₁ ≅ x₂
π A₁ B₁ , f₁      ≅s π A₂ B₂ , f₂      =
  π A₁ λ x₁ -> π A₂ λ x₂ -> x₁ ≅ x₂ ⇒ B₁ x₁ , f₁ x₁ ≅s B₂ x₂ , f₂ x₂ 
D₁ ⊛ E₁ , s₁ , t₁ ≅s D₂ ⊛ E₂ , s₂ , t₂ = D₁ , s₁ ≅s D₂ , s₂ & E₁ , t₁ ≅s E₂ , t₂
_                 ≅s _                 = bot

var i₁  , q₁      ≅e var i₂  , q₂      = i₁ ≅ i₂
π A₁ B₁ , x₁ , e₁ ≅e π A₂ B₂ , x₂ , e₂ = B₁ x₁ , e₁ ≅e B₂ x₂ , e₂
D₁ ⊛ E₁ , s₁ , e₁ ≅e D₂ ⊛ E₂ , s₂ , e₂ = D₁ , s₁ ≅s D₂ , s₂ & E₁ , e₁ ≅e E₂ , e₂
_                 ≅e _                 = bot

pattern #₀ p = node (fzero , p)
pattern #₁ p = node (fsuc fzero , p)
pattern #₂ p = node (fsuc (fsuc fzero) , p)
pattern #₃ p = node (fsuc (fsuc (fsuc fzero)) , p)
pattern #₄ p = node (fsuc (fsuc (fsuc (fsuc fzero))) , p)
pattern #₅ p = node (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))) , p)

pattern ⟨⟩₀ = node (() , _)
pattern ⟨⟩₁ = node (fsuc () , _)
pattern ⟨⟩₂ = node (fsuc (fsuc ()) , _)
pattern ⟨⟩₃ = node (fsuc (fsuc (fsuc ())) , _)
pattern ⟨⟩₄ = node (fsuc (fsuc (fsuc (fsuc ()))) , _)
pattern ⟨⟩₅ = node (fsuc (fsuc (fsuc (fsuc (fsuc ())))) , _)
