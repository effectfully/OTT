{-# OPTIONS --no-positivity-check --no-termination-check #-}

module OTT.Core where

open import Function public
open import Data.Empty public
open import Data.Unit.Base using (⊤; tt) public
open import Data.Bool.Base hiding (_≟_) public
open import Data.Nat.Base public
open import Data.List.Base hiding (zip) renaming (map to lmap) public
open import Data.List.Any using (Any; here; there) public
open import Data.List.All using (All; []; _∷_) public
open import Data.Product hiding (,_) renaming (map to pmap) public

infix 4 ,_
pattern ,_ y = _ , y


infixr 1 _&_
infixr 2 _⇒_
infix  3 _≃_ _≅_ _≅s_ _≅a_ _≅c_

data Univ : Bool -> Set

Prop = Univ false
Type = Univ true

⟦_⟧ : ∀ {k} -> Univ k -> Set

_≃_  : ∀ {k s} -> Univ k -> Univ s -> Prop
_≅_  : ∀ {k s} {A : Univ k} {B : Univ s} -> ⟦ A ⟧ -> ⟦ B ⟧ -> Prop
_≅s_ : ∀ {k s} {A : Univ k} {B : Univ s} -> List ⟦ A ⟧ -> List ⟦ B ⟧ -> Prop

Cons : Type -> Set
Cons I = ∃₂ λ k (A : Univ k) -> ⟦ A ⟧ -> List ⟦ I ⟧ × ⟦ I ⟧

Desc : Type -> Set
Desc = List ∘ Cons

module _ {I : Type} where
  Extend : (⟦ I ⟧ -> Set) -> ⟦ I ⟧ -> Cons I -> Set
  Extend F i (, A , f) = ∃ λ x -> let is , j = f x in All F is × ⟦ j ≅ i ⟧

  mutual
    record Rose (cs : Desc I) i : Set where
      inductive
      constructor node
      field childs : Childs cs cs i

    Childs : Desc I -> Desc I -> ⟦ I ⟧ -> Set
    Childs cs₁ cs₂ i = Any (Extend (Rose cs₁) i) cs₂

_≅c_ : ∀ {I₁ I₂} {cs₁ ds₁ : Desc I₁} {cs₂ ds₂ : Desc I₂} {i₂ i₁}
     -> Childs cs₁ ds₁ i₁ -> Childs cs₂ ds₂ i₂ -> Prop

data Univ where
  bot  top : Prop
  bool nat : Type
  univ : Bool -> Type
  σ    : ∀ {k s} -> (A : Univ k) -> (⟦ A ⟧ -> Univ s) -> Univ (k ∨ s)
  π    : ∀ {k s} -> (A : Univ k) -> (⟦ A ⟧ -> Univ s) -> Univ  s
  list : ∀ {k} -> Univ k -> Type
  rose : ∀ {I} -> Desc I -> ⟦ I ⟧ -> Type

⟦ bot       ⟧ = ⊥
⟦ top       ⟧ = ⊤
⟦ bool      ⟧ = Bool
⟦ nat       ⟧ = ℕ
⟦ univ k    ⟧ = Univ k
⟦ σ A B     ⟧ = ∃ λ x -> ⟦ B x ⟧
⟦ π A B     ⟧ = ∀   x -> ⟦ B x ⟧
⟦ list A    ⟧ = List ⟦ A ⟧
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

bot         ≃ bot         = top
top         ≃ top         = top
bool        ≃ bool        = top
nat         ≃ nat         = top
univ k₁     ≃ univ k₂     = k₁ ≟ᵇ k₂
σ A₁ B₁     ≃ σ A₂ B₂     = A₁ ≃ A₂ & B₁ ≅ B₂
π A₁ B₁     ≃ π A₂ B₂     = A₂ ≃ A₁ & π _ λ x₁ -> π _ λ x₂ -> x₂ ≅ x₁ ⇒ B₁ x₁ ≃ B₂ x₂
list A₁     ≃ list A₂     = A₁ ≃ A₂
rose cs₁ i₁ ≃ rose cs₂ i₂ = cs₁ ≅ cs₂ & i₂ ≅ i₁
_           ≃ _           = bot

_≅_ {A = bot        } {bot        } _   _   = top
_≅_ {A = top        } {top        } _   _   = top
_≅_ {A = bool       } {bool       } b₁  b₂  = b₁ ≟ᵇ b₂
_≅_ {A = nat        } {nat        } n₁  n₂  = n₁ ≟ⁿ n₂
_≅_ {A = univ k₁    } {univ k₂    } A₁  A₂  = A₁ ≃ A₂
_≅_ {A = σ A₁ B₁    } {σ A₂ B₂    } p₁  p₂  = let x₁ , y₁ = p₁ ; x₂ , y₂ = p₂ in x₁ ≅ x₂ & y₁ ≅ y₂
_≅_ {A = π A₁ B₁    } {π A₂ B₂    } f₁  f₂  = π _ λ x₁ -> π _ λ x₂ -> x₁ ≅ x₂ ⇒ f₁ x₁ ≅ f₂ x₂
_≅_ {A = list A₁    } {list A₂    } xs₁ xs₂ = xs₁ ≅s xs₂
_≅_ {A = rose cs₁ i₁} {rose cs₂ i₂} r₁  r₂  = let node chs₁ = r₁ ; node chs₂ = r₂ in chs₁ ≅c chs₂
_≅_                                 _   _   = bot

[]       ≅s []       = top
x₁ ∷ xs₁ ≅s x₂ ∷ xs₂ = x₁ ≅ x₂ & xs₁ ≅s xs₂
_        ≅s _        = bot

_≅a_ : ∀ {k} {A₁ A₂ : Type} {B₁ : ⟦ A₁ ⟧ -> Univ k} {B₂ : ⟦ A₂ ⟧ -> Univ k} {xs₁ xs₂}
     -> All (λ x -> ⟦ B₁ x ⟧) xs₁ -> All (λ x -> ⟦ B₂ x ⟧) xs₂ -> Prop
[]       ≅a []       = top
y₁ ∷ ys₁ ≅a y₂ ∷ ys₂ = y₁ ≅ y₂ & ys₁ ≅a ys₂
[]       ≅a y₂ ∷ ys₂ = bot
px ∷ ys₁ ≅a []       = bot

here  p₁   ≅c here  p₂   = let x₁ , rs₁ , q₁ = p₁ ; x₂ , rs₂ , q₂ = p₂ in x₁ ≅ x₂ & rs₁ ≅a rs₂
there chs₁ ≅c there chs₂ = chs₁ ≅c chs₂
here  _    ≅c there _    = bot
there _    ≅c here  _    = bot
