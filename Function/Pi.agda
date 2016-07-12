module OTT.Function.Pi where

open import OTT.Core

Tabulate : ∀ {n α} -> (Apply Enum n -> Set α) -> Set α
Tabulate {α = α} F = go _ (F ∘ tag) where
  go : ∀ n -> (Enum n -> Set α) -> Set α
  go  0            F = ⊤
  go  1            F = F tt
  go (suc (suc n)) F = F nothing × go (suc n) (F ∘ just)

tabulate : ∀ {n α} {F : Apply Enum n -> Set α} -> (∀ e -> F e) -> Tabulate F
tabulate {α = α} f = go _ (f ∘ tag) where
  go : ∀ n {F : Enum n -> Set α} -> (∀ e -> F e) -> Tabulate (F ∘ detag)
  go  0            f = tt
  go  1            f = f tt
  go (suc (suc n)) f = f nothing , go (suc n) (f ∘ just)

lookup : ∀ {n α} {F : Apply Enum n -> Set α} -> (e : Apply Enum n) -> Tabulate F -> F e
lookup {α = α} e xs = go _ (detag e) xs where
  go : ∀ n {F : Enum n -> Set α} -> (e : Enum n) -> Tabulate (F ∘ detag) -> F e
  go  0             ()
  go  1             tt       x       = x
  go (suc (suc n))  nothing (x , xs) = x
  go (suc (suc n)) (just e) (x , xs) = go (suc n) e xs

fromTuple : ∀ {n α} {F : Apply Enum n -> Set α} -> Tabulate F -> (e : Apply Enum n) -> F e
fromTuple = flip lookup

-- I tried to make a type class from this, but failed because of size issues.
-- Is there any reason to bother with `desc`?
Pi : ∀ {a β} {α : Level a} -> (A : Univ α) -> (⟦ A ⟧ -> Set β) -> Set β
Pi  bot     F = ⊤
Pi  top     F = F tt
Pi (enum n) F = Tabulate F
Pi (σ A B)  F = Pi A λ x -> Pi (B x) λ y -> F (x , y)
Pi  _       F = ∀ {x} -> F x

lam : ∀ {a β} {α : Level a} {A : Univ α} {B : ⟦ A ⟧ -> Set β} -> (∀ x -> B x) -> Pi A B
lam {A = bot   } f = tt
lam {A = top   } f = f tt
lam {A = enum n} f = tabulate f
lam {A = σ A B } g = lam λ x -> lam λ y -> g (x , y)
lam {A = nat     } f = f _
lam {A = univ _  } f = f _
lam {A = π _ _   } f = f _
lam {A = desc _ _} f = f _
lam {A = imu _ _ } f = f _

apply : ∀ {a β} {α : Level a} {A : Univ α} {F : ⟦ A ⟧ -> Set β} -> Pi A F -> (x : ⟦ A ⟧) -> F x
apply {A = bot   } f   ()
apply {A = top   } x   tt     = x
apply {A = enum n} xs  e      = lookup e xs
apply {A = σ A B } g  (x , y) = apply (apply g x) y
apply {A = nat     } y x = y
apply {A = univ _  } y x = y
apply {A = π _ _   } y x = y
apply {A = desc _ _} y x = y
apply {A = imu _ _ } y x = y
