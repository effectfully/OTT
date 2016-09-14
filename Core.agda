{-# OPTIONS --no-positivity-check --no-termination-check #-}

module OTT.Core where

open import OTT.Prelude public

infixr 1 _&_
infixr 2 _⇒_ _⇨_ _⊛_
infix  3 _≟ⁿ_ _≟ˡ_ _≈_ _≃_ _≅_ _≅ᵉ_ _≅ᵈ_ _≊ᵈ_ _≅s_ _≅e_

_≤ₘ_ : MetaLevel -> MetaLevel -> Set
a ≤ₘ b = a ⊔ₘ b ≡ b

data Level : MetaLevel -> Set where
  lzero : Level lzeroₘ
  lsuc  : ∀ {a} -> Level a -> Level (lsucₘ a)

natToMetaLevel : ℕ -> MetaLevel
natToMetaLevel  0      = lzeroₘ
natToMetaLevel (suc n) = lsucₘ (natToMetaLevel n)

natToLevel : ∀ n -> Level (natToMetaLevel n)
natToLevel  0      = lzero
natToLevel (suc n) = lsuc (natToLevel n)

_⊔_ : ∀ {a b} -> Level a -> Level b -> Level (a ⊔ₘ b)
lzero   ⊔ lzero  = lzero
lzero   ⊔ lsuc β = lsuc β
lsuc α  ⊔ lzero  = lsuc α
lsuc α  ⊔ lsuc β = lsuc (α ⊔ β)

_⊔ₘ₀_ : ∀ {a} -> MetaLevel -> Level a -> MetaLevel
a ⊔ₘ₀ lzero      = lzeroₘ
a ⊔ₘ₀ lsuc {b} β = a ⊔ₘ lsucₘ b

_⊔₀_ : ∀ {a b} -> Level a -> (β : Level b) -> Level (a ⊔ₘ₀ β)
α ⊔₀ lzero  = lzero
α ⊔₀ lsuc β = α ⊔ lsuc β

data Univ : ∀ {a} -> Level a -> Set

Univ# = Univ ∘ natToLevel
Type# = Univ# ∘ suc
Prop  = Univ# 0
Type  = λ {a} -> Univ ∘ lsuc {a}
Type₀ = Type# 0

Type₋₁ : ∀ {a} -> Level a -> Set
Type₋₁ α = Univ (lsuc lzero ⊔ α)

⟦_⟧ : ∀ {a} {α : Level a} -> Univ α -> Set

_≃_ : ∀ {a b} {α : Level a} {β : Level b} -> Univ α -> Univ β -> Prop
_≅_ : ∀ {a b} {α : Level a} {β : Level b} {A : Univ α} {B : Univ β} -> ⟦ A ⟧ -> ⟦ B ⟧ -> Prop

data Desc {i b} {ι : Level i} (I : Type ι) (β : Level b) : Set where
  var : ⟦ I ⟧ -> Desc I β
  π   : ∀ {a} {α : Level a} .{{_ : a ≤ₘ b}} -> (A : Univ α) -> (⟦ A ⟧ -> Desc I β) -> Desc I β
  _⊛_ : Desc I β -> Desc I β -> Desc I β

⟦_⟧ᵈ : ∀ {i a} {ι : Level i} {α : Level a} {I : Type ι}
     -> Desc I α -> (⟦ I ⟧ -> Set) -> Set
⟦ var i ⟧ᵈ B = B i
⟦ π A D ⟧ᵈ B = ∀ x -> ⟦ D x ⟧ᵈ B
⟦ D ⊛ E ⟧ᵈ B = ⟦ D ⟧ᵈ B × ⟦ E ⟧ᵈ B

Extend : ∀ {i a} {ι : Level i} {α : Level a} {I : Type ι}
       -> Desc I α -> (⟦ I ⟧ -> Set) -> ⟦ I ⟧ -> Set
Extend (var i) B j = ⟦ i ≅ j ⟧
Extend (π A D) B i = ∃ λ x -> Extend (D x) B i
Extend (D ⊛ E) B i = ⟦ D ⟧ᵈ B × Extend E B i

-- Funnily, Agda treats inductive records and data types differently wrt termination checking.
-- Perhaps it's not clear to Agda that induction is structural because
-- irrefutable pattern matching elaborates into function application. Do we need refutable patterns?
-- record μ {i a} {ι : Level i} {α : Level a} {I : Type ι} (D : Desc I α) j : Set where
--   inductive
--   constructor node
--   field knot : Extend D (μ D) j
-- open μ public

data μ {i a} {ι : Level i} {α : Level a} {I : Type ι} (D : Desc I α) j : Set where
  node : Extend D (μ D) j -> μ D j

knot : ∀ {i a} {ι : Level i} {α : Level a} {I : Type ι} {D : Desc I α} {j}
     -> μ D j -> Extend D (μ D) j
knot (node e) = e

_⇨_ : ∀ {i a b} {ι : Level i} {α : Level a} {β : Level b} {I : Type ι} .{{_ : a ≤ₘ b}}
    -> Univ α -> Desc I β -> Desc I β
A ⇨ D = π A λ _ -> D

data Univ where
  bot  : Prop
  top  : Prop
  nat  : Type₀
  enum : ℕ -> Type₀
  univ : ∀ {a} -> (α : Level a) -> Type α
  σ    : ∀ {a b} {α : Level a} {β : Level b} -> (A : Univ α) -> (⟦ A ⟧ -> Univ β) -> Univ (α ⊔  β)
  π    : ∀ {a b} {α : Level a} {β : Level b} -> (A : Univ α) -> (⟦ A ⟧ -> Univ β) -> Univ (α ⊔₀ β)
  desc : ∀ {a i} {ι : Level i} -> Type ι -> (α : Level a) -> Type α
  imu  : ∀ {i a} {ι : Level i} {α : Level a} {I : Type ι} -> Desc I α -> ⟦ I ⟧ -> Univ α

⟦_⟧ⁱ : ∀ {a b} {α : Level a} {β : Level b} {A : Univ α} -> (⟦ A ⟧ -> Univ β) -> ⟦ A ⟧ -> Set
⟦ B ⟧ⁱ x = ⟦ B x ⟧

⟦ bot          ⟧ = ⊥
⟦ top          ⟧ = ⊤
⟦ nat          ⟧ = ℕ
⟦ enum n       ⟧ = Apply Enum n -- `Apply` allows to make `⟦_⟧` constructor-headed.
⟦ univ α       ⟧ = Univ α
⟦ σ A B        ⟧ = ∃ ⟦ B ⟧ⁱ
⟦ π A B        ⟧ = ∀ x -> ⟦ B x ⟧
⟦ desc I α     ⟧ = Desc I α
⟦ imu D j      ⟧ = μ D j

pattern prop   = univ lzero
pattern type a = univ (lsuc a)
univ# = univ  ∘ natToLevel
type# = univ# ∘ suc

desc₋₁ : ∀ {a i} {ι : Level i} -> Type ι -> (α : Level a) -> Univ _
desc₋₁ I α = desc I (lsuc lzero ⊔ α)

_&_ : ∀ {a b} {α : Level a} {β : Level b} -> Univ α -> Univ β -> Univ (α ⊔  β)
A & B = σ A λ _ -> B

_⇒_ : ∀ {a b} {α : Level a} {β : Level b} -> Univ α -> Univ β -> Univ (α ⊔₀ β)
A ⇒ B = π A λ _ -> B

_≟ⁿ_ : ℕ -> ℕ -> Prop
0     ≟ⁿ 0     = top
suc n ≟ⁿ suc m = n ≟ⁿ m
_     ≟ⁿ _     = bot

_≟ˡ_ : ∀ {a b} -> Level a -> Level b -> Prop
lzero  ≟ˡ lzero  = top
lsuc α ≟ˡ lsuc β = α ≟ˡ β
_      ≟ˡ _      = bot

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

_≅ᵈ_ : ∀ {i₁ i₂ a₁ a₂} {ι₁ : Level i₁} {ι₂ : Level i₂}
         {α₁ : Level a₁} {α₂ : Level a₂} {I₁ : Type ι₁} {I₂ : Type ι₂}
     -> Desc I₁ α₁ -> Desc I₂ α₂ -> Prop
var i₁    ≅ᵈ var i₂    = i₁ ≅ i₂
π A₁ D₁   ≅ᵈ π A₂ D₂   = A₁ ≈ A₂ & D₁ ≅ D₂
(D₁ ⊛ E₁) ≅ᵈ (D₂ ⊛ E₂) = D₁ ≅ᵈ D₂ & E₁ ≅ᵈ E₂
_         ≅ᵈ _         = bot

_≊ᵈ_ : ∀ {i₁ i₂ a₁ a₂} {ι₁ : Level i₁} {ι₂ : Level i₂}
         {α₁ : Level a₁} {α₂ : Level a₂} {I₁ : Type ι₁} {I₂ : Type ι₂}
     -> Desc I₁ α₁ -> Desc I₂ α₂ -> Prop
_≊ᵈ_ {α₁ = lzero } {lzero } D₁ D₂ = imu D₁ ≅ imu D₂
_≊ᵈ_ {α₁ = lsuc _} {lsuc _} D₁ D₂ = D₁ ≅ᵈ D₂
_≊ᵈ_                        _  _  = bot

bot        ≃ bot        = top
top        ≃ top        = top
nat        ≃ nat        = top
enum n₁    ≃ enum n₂    = n₁ ≟ⁿ n₂
univ α₁    ≃ univ α₂    = α₁ ≟ˡ α₂
σ A₁ B₁    ≃ σ A₂ B₂    = A₁ ≈ A₂ & B₁ ≅ B₂
π A₁ B₁    ≃ π A₂ B₂    = A₂ ≈ A₁ & π A₁ λ x₁ -> π A₂ λ x₂ -> x₂ ≅ x₁ ⇒ B₁ x₁ ≈ B₂ x₂
desc I₁ α₁ ≃ desc I₂ α₂ = I₁ ≃ I₂ & α₁ ≟ˡ α₂
imu D₁ j₁  ≃ imu D₂ j₂  = D₁ ≊ᵈ D₂ & j₁ ≅ j₂
_          ≃ _          = bot

_≅e_ : ∀ {i₁ i₂ a₁ a₂ b₁ b₂} {ι₁ : Level i₁} {ι₂ : Level i₂}
         {α₁ : Level a₁} {α₂ : Level a₂} {β₁ : Level b₁} {β₂ : Level b₂}
         {I₁ : Type ι₁} {I₂ : Type ι₂} {B₁ : ⟦ I₁ ⟧ -> Univ β₁} {B₂ : ⟦ I₂ ⟧ -> Univ β₂} {j₁ j₂}
     -> (∃ λ (D₁ : Desc I₁ α₁) -> Extend D₁ ⟦ B₁ ⟧ⁱ j₁)
     -> (∃ λ (D₂ : Desc I₂ α₂) -> Extend D₂ ⟦ B₂ ⟧ⁱ j₂)
     -> Prop

_≅_ {A = bot     } {bot     } _  _  = top
_≅_ {A = top     } {top     } _  _  = top
_≅_ {A = nat     } {nat     } n₁ n₂ = n₁ ≟ⁿ n₂
_≅_ {A = enum n₁ } {enum n₂ } e₁ e₂ = n₁ , detag e₁ ≅ᵉ n₂ , detag e₂
_≅_ {A = univ α₁ } {univ α₂ } A₁ A₂ = A₁ ≈ A₂
_≅_ {A = σ A₁ B₁ } {σ A₂ B₂ } p₁ p₂ = let x₁ , y₁ = p₁ ; x₂ , y₂ = p₂ in x₁ ≅ x₂ & y₁ ≅ y₂
_≅_ {A = π A₁ B₁ } {π A₂ B₂ } f₁ f₂ = π A₁ λ x₁ -> π A₂ λ x₂ -> x₁ ≅ x₂ ⇒ f₁ x₁ ≅ f₂ x₂
_≅_ {A = desc _ _} {desc _ _} D₁ D₂ = D₁ ≅ᵈ D₂
_≅_ {A = imu D₁ _} {imu D₂ _} d₁ d₂ = D₁ , knot d₁ ≅e D₂ , knot d₂
_≅_                           _  _  = bot

_≅s_ : ∀ {i₁ i₂ a₁ a₂ b₁ b₂} {ι₁ : Level i₁} {ι₂ : Level i₂}
         {α₁ : Level a₁} {α₂ : Level a₂} {β₁ : Level b₁} {β₂ : Level b₂}
         {I₁ : Type ι₁} {I₂ : Type ι₂} {B₁ : ⟦ I₁ ⟧ -> Univ β₁} {B₂ : ⟦ I₂ ⟧ -> Univ β₂}
     -> (∃ λ (D₁ : Desc I₁ α₁) -> ⟦ D₁ ⟧ᵈ ⟦ B₁ ⟧ⁱ)
     -> (∃ λ (D₂ : Desc I₂ α₂) -> ⟦ D₂ ⟧ᵈ ⟦ B₂ ⟧ⁱ)
     -> Prop
var i₁    , x₁      ≅s var i₂    , x₂      = x₁ ≅ x₂
π A₁ D₁   , f₁      ≅s π A₂ D₂   , f₂      =
  π A₁ λ x₁ -> π A₂ λ x₂ -> x₁ ≅ x₂ ⇒ D₁ x₁ , f₁ x₁ ≅s D₂ x₂ , f₂ x₂ 
(D₁ ⊛ E₁) , s₁ , t₁ ≅s (D₂ ⊛ E₂) , s₂ , t₂ = D₁ , s₁ ≅s D₂ , s₂ & E₁ , t₁ ≅s E₂ , t₂
_                   ≅s _                   = bot

var i₁    , q₁      ≅e var i₂    , q₂      = top
π A₁ D₁   , x₁ , e₁ ≅e π A₂ D₂   , x₂ , e₂ = x₁ ≅ x₂ & D₁ x₁ , e₁ ≅e D₂ x₂ , e₂
(D₁ ⊛ E₁) , s₁ , e₁ ≅e (D₂ ⊛ E₂) , s₂ , e₂ = D₁ , s₁ ≅s D₂ , s₂ & E₁ , e₁ ≅e E₂ , e₂
_                   ≅e _                   = bot

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

pattern unit = enum 1
Unit = Apply Enum 1

pattern triv = tag tt

pos : ∀ {a} {α : Level a} -> Desc unit α
pos = var triv

mu : ∀ {a} {α : Level a} -> Desc unit α -> Univ α
mu D = imu D triv

liftDesc : ∀ {i a b} {ι : Level i} {α : Level a} {β : Level b} {I : Type ι} .{{_ : a ≤ₘ b}}
         -> Desc I α -> Desc I β
liftDesc                (var i)            = var i
liftDesc {b = b} {{q₁}} (π {c} {{q₂}} A D) =
  π {{pright (pcong (c ⊔ₘ_) q₁) (ptrans (pcong (b ⊔ₘ_) q₂) q₁)}} A λ x -> liftDesc (D x)
liftDesc                (D ⊛ E)            = liftDesc D ⊛ liftDesc E

var-inj : ∀ {i b} {ι : Level i} {I : Type ι} {β : Level b} {j₁ j₂ : ⟦ I ⟧}
        -> var {β = β} j₁ ≡ var j₂ -> j₁ ≡ j₂
var-inj prefl = prefl

⊛-inj : ∀ {i b} {ι : Level i} {I : Type ι} {β : Level b} {D₁ D₂ E₁ E₂ : Desc I β}
      -> (D₁ ⊛ E₁) ≡ (D₂ ⊛ E₂) -> D₁ ≡ D₂ × E₁ ≡ E₂
⊛-inj prefl = prefl , prefl

node-inj : ∀ {i a} {α : Level a} {ι : Level i} {I : Type ι}
             {D : Desc I α} {j} {e₁ e₂ : Extend D (μ D) j}
         -> node {D = D} e₁ ≡ node e₂ -> e₁ ≡ e₂
node-inj prefl = prefl
