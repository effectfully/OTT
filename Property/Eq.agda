-- We can do slightly better by adding something like
-- `eqable : ∀ {a} {α : Level a} -> (A : Univ α) -> Maybe (Eq A)`

module OTT.Property.Eq where

import Data.Nat.Base as Nat

open import OTT.Main

infix 4 _≟_ _≟ᵈ_

-- TODO?
module _ where
  open import Relation.Binary.PropositionalEquality.TrustMe

  contr : {A : Prop} {x y : ⟦ A ⟧} -> x ≡ y
  contr = trustMe

module _ where
  open import Data.Maybe.Base

  Tabulate : ∀ {n} -> (Apply Enum n -> Set) -> Set
  Tabulate F = go _ (F ∘ tag) where
    go : ∀ n -> (Enum n -> Set) -> Set
    go  0            F = ⊤
    go  1            F = F tt
    go (suc (suc n)) F = F nothing × go (suc n) (F ∘ just)

  lookup : ∀ {n} {F : Apply Enum n -> Set} -> (e : Apply Enum n) -> Tabulate F -> F e
  lookup e xs = go _ (detag e) xs where
    go : ∀ n {F : Enum n -> Set} -> (e : Enum n) -> Tabulate (F ∘ detag) -> F e
    go  0             ()
    go  1             tt       x       = x
    go (suc (suc n))  nothing (x , xs) = x
    go (suc (suc n)) (just e) (x , xs) = go (suc n) e xs

-- We could compare functions with a finite domain for equality.
mutual
  SemEq : ∀ {i a} {α : Level a} {I : Type i} -> Desc I α -> Set
  SemEq (var i) = ⊤
  SemEq (π A D) = ⊥
  SemEq (D ⊛ E) = SemEq D × SemEq E

  ExtendEq : ∀ {i a} {α : Level a} {I : Type i} -> Desc I α -> Set
  ExtendEq (var i) = ⊤
  ExtendEq (π A D) = Eq A × Pi A λ x -> ExtendEq (D x)
  ExtendEq (D ⊛ E) = SemEq D × ExtendEq E

  Eq : ∀ {a} {α : Level a} -> Univ α -> Set
  Eq  bot       = ⊤
  Eq  top       = ⊤
  Eq (α ≡ˢˡ β)  = ⊥
  Eq  nat       = ⊤
  Eq (enum n)   = ⊤
  Eq (univ α)   = ⊥
  Eq (σ A B)    = Eq A × Pi A λ x -> Eq (B x)
  Eq (π A B)    = ⊥
  Eq (desc I α) = Eq I
  Eq (imu D j)  = ExtendEq D

  -- Should there be a separate type class for `imu`?
  -- Is there any reason to bother with `desc`?
  Pi : ∀ {a} {α : Level a} -> (A : Univ α) -> (⟦ A ⟧ -> Set) -> Set
  Pi  bot     F = ⊤
  Pi  top     F = F tt
  Pi (enum n) F = Tabulate F
  Pi (σ A B)  F = Pi A λ x -> Pi (B x) λ y -> F (x , y)
  Pi  _       F = ∀ {x} -> F x

-- Begs for a view, but I don't want to mess with instance arguments.
apply : ∀ {a} {α : Level a} {A : Univ α} {F : ⟦ A ⟧ -> Set} -> Pi A F -> (x : ⟦ A ⟧) -> F x
apply {A = bot   } f   ()
apply {A = top   } x   tt     = x
apply {A = enum n} xs  e      = lookup e xs
apply {A = σ A B } g  (x , y) = apply (apply g x) y
apply {A = _ ≡ˢˡ  _} y x = y
apply {A = nat     } y x = y
apply {A = univ _  } y x = y
apply {A = π _ _   } y x = y
apply {A = desc _ _} y x = y
apply {A = imu _ _ } y x = y

{-# TERMINATING #-}
mutual
  _≟ᵈ_ : ∀ {i a} {α : Level a} {I : Type i} {{eqI : Eq I}} -> IsPartSet (Desc I α)
  var i₁    ≟ᵈ var i₂    = dcong var var-inj (i₁ ≟ i₂)
  π A₁ D₁   ≟ᵈ π A₂ D₂   = none -- The only undecidable part.
  (D₁ ⊛ E₁) ≟ᵈ (D₂ ⊛ E₂) = dcong₂ _⊛_ ⊛-inj (D₁ ≟ᵈ D₂) (E₁ ≟ᵈ E₂)
  var _     ≟ᵈ π _ _     = no λ()
  var _     ≟ᵈ (_ ⊛ _)   = no λ()
  π _ _     ≟ᵈ var _     = no λ()
  π _ _     ≟ᵈ (_ ⊛ _)   = no λ()
  (_ ⊛ _)   ≟ᵈ var _     = no λ()
  (_ ⊛ _)   ≟ᵈ π _ _     = no λ()

  decSem : ∀ {i a p} {α : Level a} {φ : Level p} {I : Type i}
             {F : ⟦ I ⟧ -> Univ φ} {{eqF : ∀ {i} -> Eq (F i)}}
         -> (D : Desc I α) {{eqD : SemEq D}} -> IsPartSet (⟦ D ⟧ᵈ ⟦ F ⟧ᵒ)
  decSem (var i)                x₁        x₂       = x₁ ≟ x₂ 
  decSem (π A D) {{()}}
  decSem (D ⊛ E) {{eqD , eqE}} (s₁ , t₁) (s₂ , t₂) =
    decSem D {{eqD}} s₁ s₂ <,>ᵈ decSem E {{eqE}} t₁ t₂

  decExtend : ∀ {i a p} {α : Level a} {φ : Level p} {I : Type i} {j}
                {F : ⟦ I ⟧ -> Univ φ} {{eqF : ∀ {i} -> Eq (F i)}}
            -> (D : Desc I α) {{eqD : ExtendEq D}} -> IsPartSet (Extend D ⟦ F ⟧ᵒ j)
  decExtend (var i)                q₁        q₂       = yes contr
  decExtend (π A D) {{eqA , eqD}} (x₁ , e₁) (x₂ , e₂) =
    _≟_ {{eqA}} x₁ x₂ <,>ᵈᵒ decExtend (D x₁) {{apply eqD x₁}} e₁
  decExtend (D ⊛ E) {{eqD , eqE}} (s₁ , e₁) (s₂ , e₂) =
    decSem D {{eqD}} s₁ s₂ <,>ᵈ decExtend E {{eqE}} e₁ e₂

  _≟_ : ∀ {a} {α : Level a} {A : Univ α} {{eqA : Eq A}} -> IsPartSet ⟦ A ⟧
  _≟_ {A = bot     }                ()        ()
  _≟_ {A = top     }                tt        tt       = yes prefl
  _≟_ {A = α ≡ˢˡ β } {{()}}
  _≟_ {A = nat     }                n₁        n₂       = decToPartDec (n₁ Nat.≟ n₂)
  _≟_ {A = enum n  }               (tag e₁)  (tag e₂)  =
    dcong tag tag-inj (decToPartDec (decEnum n e₁ e₂))
  _≟_ {A = univ α  } {{()}}
  _≟_ {A = σ A B   } {{eqA , eqB}} (x₁ , y₁) (x₂ , y₂) =
    _≟_ {{eqA}} x₁ x₂ <,>ᵈᵒ _≟_ {{apply eqB x₁}} y₁
  _≟_ {A = π A B   } {{()}}
  _≟_ {A = desc I α}                D₁        D₂       = D₁ ≟ᵈ D₂
  _≟_ {A = imu D j }               (node e₁) (node e₂) = dcong node node-inj (decExtend D e₁ e₂)

private
  module Test where
    open import OTT.Data.Fin
    open import OTT.Data.Sum
    open import OTT.Data.List

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
