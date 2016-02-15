{-# OPTIONS --no-positivity-check --no-termination-check #-}

module OTT.Tele.Core where

open import OTT.Prelude

record Unit : Set where
  constructor triv

infixr 1 _&_
infixr 2 _⇒_
infix  3 _≈_ _≃_ _≅_ _≅s_ _≅t_ _≅f_ _≅a_ _≅e_ _≅c_

data Univ : Bool -> Set

Prop = Univ false
Type = Univ true

⟦_⟧ : ∀ {k} -> Univ k -> Set

_≈_  : ∀ {k s} -> Univ k -> Univ s -> Prop
_≃_  : ∀ {k s} -> Univ k -> Univ s -> Prop
_≅_  : ∀ {k s} {A : Univ k} {B : Univ s} -> ⟦ A ⟧ -> ⟦ B ⟧ -> Prop
_≅s_ : ∀ {k s} {A : Univ k} {B : Univ s} -> List ⟦ A ⟧ -> List ⟦ B ⟧ -> Prop

-- Avoiding size issues using the induction-recursion shrink ray.
-- Otherwise it would be the Freer monad over the identity functor.
data Tele (B : Set) : Set where
  ret : B -> Tele B
  sig : ∀ {k} -> (A : Univ k) -> (⟦ A ⟧ -> Tele B) -> Tele B

Fold : ∀ {B} -> (B -> Set) -> Tele B -> Set
Fold G (ret y)   = G y
Fold G (sig A k) = ∀ x -> Fold G (k x)

Cons : Type -> Set
Cons I = Tele (List (Tele ⟦ I ⟧) × ⟦ I ⟧)

Desc : Type -> Set
Desc = List ∘ Cons

module _ {I : Type} where
  Extend : (⟦ I ⟧ -> Set) -> ⟦ I ⟧ -> Cons I -> Set
  Extend F i (ret (ts , j)) = All (Fold F) ts × ⟦ j ≅ i ⟧
  Extend F i (sig  A k)     = ∃ λ x -> Extend F i (k x)

  mutual
    record Rose (cs : Desc I) i : Set where
      inductive
      constructor node
      field childs : Childs cs cs i

    Childs : Desc I -> Desc I -> ⟦ I ⟧ -> Set
    Childs cs₁ cs₂ i = Any (Extend (Rose cs₁) i) cs₂

_≅t_ : {A B : Type} -> Tele ⟦ A ⟧ -> Tele ⟦ B ⟧ -> Prop
_≅c_ : ∀ {I₁ I₂} {cs₁ ds₁ : Desc I₁} {cs₂ ds₂ : Desc I₂} {i₂ i₁}
     -> Childs cs₁ ds₁ i₁ -> Childs cs₂ ds₂ i₂ -> Prop

data Univ where
  bot  top : Prop
  unit nat : Type
  univ : Bool -> Type
  σ    : ∀ {k s} -> (A : Univ k) -> (⟦ A ⟧ -> Univ s) -> Univ (k ∨ s)
  π    : ∀ {k s} -> (A : Univ k) -> (⟦ A ⟧ -> Univ s) -> Univ  s
  list : ∀ {k} -> Univ k -> Type
  tele : Type -> Type
  rose : ∀ {I} -> Desc I -> ⟦ I ⟧ -> Type

⟦ bot       ⟧ = ⊥
⟦ top       ⟧ = ⊤
⟦ unit      ⟧ = Unit
⟦ nat       ⟧ = ℕ
⟦ univ k    ⟧ = Univ k
⟦ σ A B     ⟧ = ∃ λ x -> ⟦ B x ⟧
⟦ π A B     ⟧ = ∀   x -> ⟦ B x ⟧
⟦ list A    ⟧ = List ⟦ A ⟧
⟦ tele A    ⟧ = Tele ⟦ A ⟧
⟦ rose cs i ⟧ = Rose cs i

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

_≈_ {false} {false} A₁ A₂ = A₁ ⇒ A₂ & A₂ ⇒ A₁
_≈_ {true } {true } A₁ A₂ = A₁ ≃ A₂
_≈_                 _  _  = bot

bot         ≃ bot         = top
top         ≃ top         = top
unit        ≃ unit        = top
nat         ≃ nat         = top
univ k₁     ≃ univ k₂     = k₁ ≟ᵇ k₂
σ A₁ B₁     ≃ σ A₂ B₂     = A₁ ≈ A₂ & B₁ ≅ B₂
π A₁ B₁     ≃ π A₂ B₂     = A₂ ≈ A₁ & π _ λ x₁ -> π _ λ x₂ -> x₂ ≅ x₁ ⇒ B₁ x₁ ≈ B₂ x₂
list A₁     ≃ list A₂     = A₁ ≈ A₂
tele A₁     ≃ tele A₂     = A₁ ≈ A₂
rose cs₁ i₁ ≃ rose cs₂ i₂ = cs₁ ≅ cs₂ & i₂ ≅ i₁
_           ≃ _           = bot

_≅_ {A = bot        } {bot        } _   _   = top
_≅_ {A = top        } {top        } _   _   = top
_≅_ {A = unit       } {unit       } _   _   = top
_≅_ {A = nat        } {nat        } n₁  n₂  = n₁ ≟ⁿ n₂
_≅_ {A = univ k₁    } {univ k₂    } A₁  A₂  = A₁ ≈ A₂
_≅_ {A = σ A₁ B₁    } {σ A₂ B₂    } p₁  p₂  = let x₁ , y₁ = p₁ ; x₂ , y₂ = p₂ in x₁ ≅ x₂ & y₁ ≅ y₂
_≅_ {A = π A₁ B₁    } {π A₂ B₂    } f₁  f₂  = π _ λ x₁ -> π _ λ x₂ -> x₁ ≅ x₂ ⇒ f₁ x₁ ≅ f₂ x₂
_≅_ {A = list A₁    } {list A₂    } xs₁ xs₂ = xs₁ ≅s xs₂
_≅_ {A = tele A₁    } {tele A₂    } t₁  t₂  = t₁  ≅t t₂
_≅_ {A = rose cs₁ i₁} {rose cs₂ i₂} r₁  r₂  = let node chs₁ = r₁ ; node chs₂ = r₂ in chs₁ ≅c chs₂
_≅_                                 _   _   = bot

[]       ≅s []       = top
x₁ ∷ xs₁ ≅s x₂ ∷ xs₂ = x₁ ≅ x₂ & xs₁ ≅s xs₂
_        ≅s _        = bot

ret x₁    ≅t ret x₂    = x₁ ≅ x₂
sig A₁ k₁ ≅t sig A₂ k₂ = k₁ ≅ k₂
_         ≅t _         = bot

_≅f_ : ∀ {k s} {A₁ A₂ : Type} {B₁ : ⟦ A₁ ⟧ -> Univ k} {B₂ : ⟦ A₂ ⟧ -> Univ s}
     -> ∃ (Fold (λ x -> ⟦ B₁ x ⟧)) -> ∃ (Fold (λ x -> ⟦ B₂ x ⟧)) -> Prop
ret x₁    , y₁ ≅f ret x₂    , y₂ = x₁ ≅ x₂ & y₁ ≅ y₂
sig A₁ k₁ , f₁ ≅f sig A₂ k₂ , f₂ = π A₁ λ x₁ -> π A₂ λ x₂ -> x₁ ≅ x₂ ⇒ k₁ x₁ , f₁ x₁ ≅f k₂ x₂ , f₂ x₂
_              ≅f _              = bot

_≅a_ : ∀ {k s} {A₁ A₂ : Type} {B₁ : ⟦ A₁ ⟧ -> Univ k} {B₂ : ⟦ A₂ ⟧ -> Univ s} {is₁ is₂}
     -> All (Fold (λ x -> ⟦ B₁ x ⟧)) is₁ -> All (Fold (λ x -> ⟦ B₂ x ⟧)) is₂ -> Prop
[]                  ≅a []                  = top
_∷_ {x = t₁} f₁ fs₁ ≅a _∷_ {x = t₂} f₂ fs₂ = t₁ , f₁ ≅f t₂ , f₂ & fs₁ ≅a fs₂
_                   ≅a _                   = bot

_≅e_ : ∀ {I₁ I₂} {F₁ : ⟦ I₁ ⟧ -> Type} {F₂ : ⟦ I₂ ⟧ -> Type} {i₁ i₂}
     -> ∃ (Extend (λ x -> ⟦ F₁ x ⟧) i₁) -> ∃ (Extend (λ x -> ⟦ F₂ x ⟧) i₂) -> Prop
ret (t₁ , i₁) , fs₁ , q₁ ≅e ret (t₂ , i₂) , fs₂ , q₂ = i₁ ≅ i₂ & fs₁ ≅a fs₂
sig A₁ k₁     , x₁  , e₁ ≅e sig A₂ k₂     , x₂  , e₂ = x₁ ≅ x₂ & k₁ x₁ , e₁ ≅e k₂ x₂ , e₂
_                        ≅e _                        = bot

here {x = c₁} e₁ ≅c here {x = c₂} e₂ = c₁ , e₁ ≅e c₂ , e₂
there chs₁       ≅c there chs₂       = chs₁ ≅c chs₂
_                ≅c _                = bot

pattern #₀ y = node (here y)
pattern #₁ y = node (there (here y))
pattern #₂ y = node (there (there (here y)))
pattern #₃ y = node (there (there (there (here y))))
pattern #₄ y = node (there (there (there (there (here y)))))
pattern #₅ y = node (there (there (there (there (there (here y))))))

pattern ⟨⟩₁ = node (there ())
pattern ⟨⟩₂ = node (there (there ()))
pattern ⟨⟩₃ = node (there (there (there ())))
pattern ⟨⟩₄ = node (there (there (there (there ()))))
pattern ⟨⟩₅ = node (there (there (there (there (there ())))))
