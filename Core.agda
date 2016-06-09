{-# OPTIONS --no-positivity-check --no-termination-check #-}

module OTT.Core where

open import OTT.Prelude

infixr 1 _&_
infixr 2 _⇒_ _⊛_
infix  3 _≈_ _≃_ _≅_ _≅ᵉ_ _≅ᵈ_ _≊ᵈ_ _≅s_ _≅e_

data Level : MetaLevel -> Set where
  lzero : Level lzeroₘ
  lsuc  : ∀ a -> Level (lsucₘ a)

data SomeLevel : Set where
  meta  : MetaLevel -> SomeLevel
  level : ∀ {a} -> Level a -> SomeLevel

natToMetaLevel : ℕ -> MetaLevel
natToMetaLevel  0      = lzeroₘ
natToMetaLevel (suc n) = lsucₘ (natToMetaLevel n)

natToLevel : ∀ n -> Level (natToMetaLevel n)
natToLevel  0      = lzero
natToLevel (suc n) = lsuc (natToMetaLevel n)

_⊔_ : ∀ {a b} -> Level a -> Level b -> Level (a ⊔ₘ b)
lzero   ⊔ lzero  = lzero
lzero   ⊔ lsuc b = lsuc b
lsuc a  ⊔ lzero  = lsuc a
lsuc a  ⊔ lsuc b = lsuc (a ⊔ₘ b)

_⊔ₘ₀_ : ∀ {a} -> MetaLevel -> Level a -> MetaLevel
a ⊔ₘ₀ lzero  = lzeroₘ
a ⊔ₘ₀ lsuc b = a ⊔ₘ lsucₘ b

_⊔₀_ : ∀ {a b} -> Level a -> (β : Level b) -> Level (a ⊔ₘ₀ β)
α ⊔₀ lzero  = lzero
α ⊔₀ lsuc b = α ⊔ lsuc b

meta-inj : ∀ {a b} -> meta a ≡ meta b -> a ≡ b
meta-inj prefl = prefl

Enum : ℕ -> Set
Enum  0            = ⊥
Enum  1            = ⊤
Enum (suc (suc n)) = Maybe (Enum (suc n))

data Univ : ∀ {a} -> Level a -> Set

Prop = Univ lzero
Type = Univ ∘ lsuc

⟦_⟧ : ∀ {a} {α : Level a} -> Univ α -> Set

_≃_ : ∀ {a b} {α : Level a} {β : Level b} -> Univ α -> Univ β -> Prop
_≅_ : ∀ {a b} {α : Level a} {β : Level b} {A : Univ α} {B : Univ β} -> ⟦ A ⟧ -> ⟦ B ⟧ -> Prop

data UDesc {i o} (I : Type i) (ω : Level o) : MetaLevel -> Set where
  var[_] : ∀ {a} -> o ≡ a -> ⟦ I ⟧ -> UDesc I ω a
  π[_]   : ∀ {a b} {α : Level a}
         -> .(a ⊔ₘ o ≡ b) -> (A : Univ α) -> (⟦ A ⟧ -> UDesc I ω b) -> UDesc I ω b
  _⊛_    : ∀ {o} -> UDesc I ω o -> UDesc I ω o -> UDesc I ω o

pattern var′ i   = var[ _ ] i
pattern π′ A D   = π[ _ ] A D

Desc : ∀ {a i} -> Type i -> Level a -> Set
Desc {a} I α = UDesc I α a

⟦_⟧ᵈ  : ∀ {i o a} {ω : Level o} {I : Type i} -> UDesc I ω a -> (⟦ I ⟧ -> Set) -> Set
⟦ var′ i ⟧ᵈ F = F i
⟦ π′ A D ⟧ᵈ F = ∀ x -> ⟦ D x ⟧ᵈ F
⟦ D ⊛ E  ⟧ᵈ F = ⟦ D ⟧ᵈ F × ⟦ E ⟧ᵈ F

Extend : ∀ {i o a} {ω : Level o} {I : Type i} -> UDesc I ω a -> (⟦ I ⟧ -> Set) -> ⟦ I ⟧ -> Set
Extend (var′ j) F i = ⟦ j ≅ i ⟧
Extend (π′ A D) F i = ∃ λ x -> Extend (D x) F i
Extend (D ⊛ E ) F i = ⟦ D ⟧ᵈ F × Extend E F i

data Univ where
  bot    : Prop
  top    : Prop
  _≡ˢˡ_  : SomeLevel -> SomeLevel -> Prop
  nat    : Type lzeroₘ
  enum   : ℕ -> Type lzeroₘ
  univ   : ∀ {a} -> Level a -> Type a
  σ      : ∀ {a b} {α : Level a} {β : Level b}
         -> (A : Univ α) -> (⟦ A ⟧ -> Univ β) -> Univ (α ⊔  β)
  π      : ∀ {a b} {α : Level a} {β : Level b}
         -> (A : Univ α) -> (⟦ A ⟧ -> Univ β) -> Univ (α ⊔₀ β)
  udesc  : ∀ {o i} -> Type i -> Level o -> ∀ a -> Type a
  extend : ∀ {i o a b} {ω : Level o} {β : Level b} {I : Type i}
         -> UDesc I ω a -> (⟦ I ⟧ -> Univ β) -> ⟦ I ⟧ -> Univ β
  imu    : ∀ {i a} {α : Level a} {I : Type i} -> Desc I α -> ⟦ I ⟧ -> Univ α

record μ {i a} {α : Level a} {I : Type i} (D : Desc I α) i : Set where
  inductive
  constructor node
  field knot : Extend D (μ D) i

-- `Apply` and `Wrap` allow to make `⟦_⟧` constructor-headed.
⟦ bot          ⟧ = ⊥
⟦ top          ⟧ = ⊤
⟦ α ≡ˢˡ β      ⟧ = α ≡ β
⟦ nat          ⟧ = ℕ
⟦ enum n       ⟧ = Apply Enum n
⟦ univ α       ⟧ = Univ α
⟦ σ A B        ⟧ = ∃ λ x -> ⟦ B x ⟧
⟦ π A B        ⟧ = ∀   x -> ⟦ B x ⟧
⟦ udesc I ω a  ⟧ = UDesc I ω a
⟦ extend D F i ⟧ = Wrap (Extend D (⟦_⟧ ∘ F) i)
⟦ imu D i      ⟧ = μ D i

univ# = univ ∘ natToLevel
prop  = univ# 0
type  = univ# ∘ suc

_&_ : ∀ {a b} {α : Level a} {β : Level b} -> Univ α -> Univ β -> Univ (α ⊔  β)
A & B = σ A λ _ -> B

_⇒_ : ∀ {a b} {α : Level a} {β : Level b} -> Univ α -> Univ β -> Univ (α ⊔₀ β)
A ⇒ B = π A λ _ -> B

desc : ∀ {a i} -> Type i -> Level a -> Type a
desc {a} I α = udesc I α a

_≟ⁿ_ : ℕ -> ℕ -> Prop
0     ≟ⁿ 0     = top
suc n ≟ⁿ suc m = n ≟ⁿ m
_     ≟ⁿ _     = bot

_≅ᵉ_ : ∃ Enum -> ∃ Enum -> Prop
0            , ()      ≅ᵉ 0            , ()
1            , tt      ≅ᵉ 1            , tt      = top
suc (suc n₁) , nothing ≅ᵉ suc (suc n₂) , nothing = top
suc (suc n₁) , just e₁ ≅ᵉ suc (suc n₂) , just e₂ = suc n₁ , e₁ ≅ᵉ suc n₂ , e₂
_                      ≅ᵉ _                      = bot

_≈_ : ∀ {a b} {α : Level a} {β : Level b} -> Univ α -> Univ β -> Prop
_≈_ {α = lzero } {lzero } A₁ A₂ = A₁ ⇒ A₂ & A₂ ⇒ A₁
_≈_ {α = lsuc _} {lsuc _} A₁ A₂ = A₁ ≃ A₂
_≈_                       _  _  = bot

_≅ᵈ_ : ∀ {i₁ i₂ o₁ o₂ a₁ a₂} {ω₁ : Level o₁} {ω₂ : Level o₂} {I₁ : Type i₁} {I₂ : Type i₂}
     -> UDesc I₁ ω₁ a₁ -> UDesc I₂ ω₂ a₂ -> Prop
var′ i₁   ≅ᵈ var′ i₂   = i₁ ≅ i₂
π′ A₁ D₁  ≅ᵈ π′ A₂ D₂  = A₁ ≈ A₂ & π A₁ λ x₁ -> π A₂ λ x₂ -> x₁ ≅ x₂ ⇒ D₁ x₁ ≅ᵈ D₂ x₂
(D₁ ⊛ E₁) ≅ᵈ (D₂ ⊛ E₂) = D₁ ≅ᵈ D₂ & E₁ ≅ᵈ E₂
_         ≅ᵈ _         = bot

_≊ᵈ_ : ∀ {i₁ i₂ a₁ a₂} {α₁ : Level a₁} {α₂ : Level a₂} {I₁ : Type i₁} {I₂ : Type i₂}
     -> Desc I₁ α₁ -> Desc I₂ α₂ -> Prop
_≊ᵈ_ {α₁ = lzero } {lzero } D₁ D₂ = extend D₁ (imu D₁) ≅ extend D₂ (imu D₂)
_≊ᵈ_ {α₁ = lsuc _} {lsuc _} D₁ D₂ = D₁ ≅ᵈ D₂
_≊ᵈ_ {α₁ = lzero } {lsuc _} D₁ D₂ = bot
_≊ᵈ_ {α₁ = lsuc _} {lzero } D₁ D₂ = bot

bot                ≃ bot                = top
top                ≃ top                = top
(α₁ ≡ˢˡ β₁)        ≃ (α₂ ≡ˢˡ β₂)        = α₁ ≡ˢˡ α₂ & β₁ ≡ˢˡ β₂
nat                ≃ nat                = top
enum n₁            ≃ enum n₂            = n₁ ≟ⁿ n₂
univ α₁            ≃ univ α₂            = level α₁ ≡ˢˡ level α₂
σ A₁ B₁            ≃ σ A₂ B₂            = A₁ ≈ A₂ & B₁ ≅ B₂
π A₁ B₁            ≃ π A₂ B₂            = A₂ ≈ A₁ & π A₁ λ x₁ -> π A₂ λ x₂ -> x₂ ≅ x₁ ⇒ B₁ x₁ ≈ B₂ x₂
udesc {o₁} I₁ _ a₁ ≃ udesc {o₂} I₂ _ a₂ = I₁ ≃ I₂ & meta o₁ ≡ˢˡ meta o₂ & meta a₁ ≡ˢˡ meta a₂
extend D₁ F₁ i₁    ≃ extend D₂ F₂ i₂    = D₁ ≅ᵈ D₂ & F₁ ≅ F₂ & i₁ ≅ i₂
imu D₁ i₁          ≃ imu D₂ i₂          = D₁ ≊ᵈ D₂ & i₁ ≅ i₂
_                  ≃ _                  = bot

_≅e_ : ∀ {i₁ i₂ o₁ o₂ a₁ a₂ b₁ b₂}
         {ω₁ : Level o₁} {ω₂ : Level o₂} {β₁ : Level b₁} {β₂ : Level b₂}
         {I₁ : Type i₁} {I₂ : Type i₂} {F₁ : ⟦ I₁ ⟧ -> Univ β₁} {F₂ : ⟦ I₂ ⟧ -> Univ β₂} {j₁ j₂}
     -> (∃ λ (D₁ : UDesc I₁ ω₁ a₁) -> Extend D₁ (λ x₁ -> ⟦ F₁ x₁ ⟧) j₁)
     -> (∃ λ (D₂ : UDesc I₂ ω₂ a₂) -> Extend D₂ (λ x₂ -> ⟦ F₂ x₂ ⟧) j₂)
     -> Prop

_≅_ {A = bot          } {bot          } _  _  = top
_≅_ {A = top          } {top          } _  _  = top
_≅_ {A = α₁ ≡ˢˡ β₁    } {α₂ ≡ˢˡ β₂    } _  _  = top
_≅_ {A = nat          } {nat          } n₁ n₂ = n₁ ≟ⁿ n₂
_≅_ {A = enum n₁      } {enum n₂      } e₁ e₂ = n₁ , detag e₁ ≅ᵉ n₂ , detag e₂
_≅_ {A = univ α₁      } {univ α₂      } A₁ A₂ = A₁ ≈ A₂
_≅_ {A = σ A₁ B₁      } {σ A₂ B₂      } p₁ p₂ = let x₁ , y₁ = p₁ ; x₂ , y₂ = p₂ in x₁ ≅ x₂ & y₁ ≅ y₂
_≅_ {A = π A₁ B₁      } {π A₂ B₂      } f₁ f₂ = π A₁ λ x₁ -> π A₂ λ x₂ -> x₁ ≅ x₂ ⇒ f₁ x₁ ≅ f₂ x₂
_≅_ {A = udesc _ _ _  } {udesc _ _ _  } D₁ D₂ = D₁ ≅ᵈ D₂
_≅_ {A = extend D₁ _ _} {extend D₂ _ _} e₁ e₂ = D₁ , unwrap e₁ ≅e D₂ , unwrap e₂
_≅_ {A = imu D₁ _     } {imu D₂ _     } a₁ a₂ = let node e₁ = a₁; node e₂ = a₂ in D₁ , e₁ ≅e D₂ , e₂
_≅_                                     _  _  = bot

_≅s_ : ∀ {i₁ i₂ o₁ o₂ a₁ a₂ b₁ b₂}
         {ω₁ : Level o₁} {ω₂ : Level o₂} {β₁ : Level b₁} {β₂ : Level b₂}
         {I₁ : Type i₁} {I₂ : Type i₂} {F₁ : ⟦ I₁ ⟧ -> Univ β₁} {F₂ : ⟦ I₂ ⟧ -> Univ β₂}
     -> (∃ λ (D₁ : UDesc I₁ ω₁ a₁) -> ⟦ D₁ ⟧ᵈ λ x₁ -> ⟦ F₁ x₁ ⟧)
     -> (∃ λ (D₂ : UDesc I₂ ω₂ a₂) -> ⟦ D₂ ⟧ᵈ λ x₂ -> ⟦ F₂ x₂ ⟧)
     -> Prop
var′ i₁   , x₁      ≅s var′ i₂   , x₂      = x₁ ≅ x₂
π′ A₁ D₁  , f₁      ≅s π′ A₂ D₂  , f₂      =
  π A₁ λ x₁ -> π A₂ λ x₂ -> x₁ ≅ x₂ ⇒ D₁ x₁ , f₁ x₁ ≅s D₂ x₂ , f₂ x₂ 
(D₁ ⊛ E₁) , s₁ , t₁ ≅s (D₂ ⊛ E₂) , s₂ , t₂ = D₁ , s₁ ≅s D₂ , s₂ & E₁ , t₁ ≅s E₂ , t₂
_                   ≅s _                   = bot

var′ i₁   , r₁      ≅e var′ i₂   , r₂      = i₁ ≅ i₂
π′ A₁ D₁  , x₁ , e₁ ≅e π′ A₂ D₂  , x₂ , e₂ = D₁ x₁ , e₁ ≅e D₂ x₂ , e₂
(D₁ ⊛ E₁) , s₁ , e₁ ≅e (D₂ ⊛ E₂) , s₂ , e₂ = D₁ , s₁ ≅s D₂ , s₂ & E₁ , e₁ ≅e E₂ , e₂
_                   ≅e _                   = bot

module _ {i o} {ω : Level o} {I : Type i} where
  infixr 2 _⇒ᵈ_

  var : ⟦ I ⟧ -> Desc I ω
  var = var[ prefl ]

  πᵈ : ∀ {a} {α : Level a}
     -> (A : Univ α) -> (⟦ A ⟧ -> UDesc I ω (a ⊔ₘ o)) -> UDesc I ω (a ⊔ₘ o)
  πᵈ = π[ prefl ]

  _⇒ᵈ_ : ∀ {a} {α : Level a}
       -> (A : Univ α) -> UDesc I ω (a ⊔ₘ o) -> UDesc I ω (a ⊔ₘ o)
  A ⇒ᵈ D = πᵈ A λ _ -> D

pattern #₀ p = node (tag  nothing                                   , p)
pattern #₁ p = node (tag (just nothing)                             , p)
pattern #₂ p = node (tag (just (just nothing))                      , p)
pattern #₃ p = node (tag (just (just (just nothing)))               , p)
pattern #₄ p = node (tag (just (just (just (just nothing))))        , p)
pattern #₅ p = node (tag (just (just (just (just (just nothing))))) , p)

pattern !#₀ p = node (tag  tt                                   , p)
pattern !#₁ p = node (tag (just tt)                             , p)
pattern !#₂ p = node (tag (just (just tt))                      , p)
pattern !#₃ p = node (tag (just (just (just tt)))               , p)
pattern !#₄ p = node (tag (just (just (just (just tt))))        , p)
pattern !#₅ p = node (tag (just (just (just (just (just tt))))) , p)

unit = enum 1
Unit = Apply Enum 1

triv : Unit
triv = tag tt

pos : ∀ {a} {α : Level a} -> Desc unit α
pos = var triv

mu : ∀ {a} {α : Level a} -> Desc unit α -> Univ α
mu D = imu D triv
