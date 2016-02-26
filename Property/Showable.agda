{-# OPTIONS --no-termination-check #-}

module OTT.Property.Showable where

open import OTT.Main

open import Data.Char as Char hiding (show)
open import Data.String.Base hiding (show) renaming (_++_ to _s++_)
import Data.Nat.Show as Nat

instance
  Σ-instance : ∀ {α β} {A : Set α} {B : A -> Set β} {{x : A}} {{y : B x}} -> Σ A B
  Σ-instance {{x}} {{y}} = x , y

  All-[] : ∀ {α β} {A : Set α} {B : A -> Set β} -> All B []
  All-[] = []

  All-∷ : ∀ {α β} {A : Set α} {B : A -> Set β} {x xs}
            {{y : B x}} {{ys : All B xs}} -> All B (x ∷ xs)
  All-∷ {{y}} {{ys}} = y ∷ ys

unmap : ∀ {α β γ} {A : Set α} {B : A -> Set β} {C : Set γ} {xs}
       -> (∀ {x} -> B x -> C) -> All B xs -> List C
unmap g  []      = []
unmap g (y ∷ ys) = g y ∷ unmap g ys

zipAll : ∀ {α β γ} {A : Set α} {B : A -> Set β} {C : A -> Set γ} {xs}
       -> All B xs -> All C xs -> All (λ x -> B x × C x) xs
zipAll  []       []      = []
zipAll (y ∷ ys) (z ∷ zs) = (y , z) ∷ zipAll ys zs

recAllAny : ∀ {α β γ δ} {A : Set α} {B : A -> Set β} {C : A -> Set γ} {D : Set δ} {xs}
          -> (∀ {x} -> B x -> C x -> D) -> All B xs -> Any C xs -> D
recAllAny g (y ∷ ys) (here  z) = g y z
recAllAny g (y ∷ ys) (there a) = recAllAny g ys a

sconcat : List String -> String
sconcat = foldr _s++_ ""

parens : String -> String
parens s = "(" s++ s s++ ")"

record Named {I} (cs : Desc I) : Set where
  field names : All (λ _ -> String) cs
open Named public

mutual
  ShowableTele : ∀ {A} -> Tele A -> Set
  ShowableTele (ret x)  = ⊤
  ShowableTele (pi A B) = Showable A × ∀ x -> ShowableTele (B x)

  Showable : ∀ {k} -> Univ k -> Set
  Showable  bot        = ⊥
  Showable  top        = ⊤
  Showable  unit       = ⊤
  Showable  nat        = ⊤
  Showable (univ k)    = ⊥
  Showable (σ A B)     = Showable A × ∀ x -> Showable (B x)
  Showable (π A B)     = ⊥
  Showable (list A)    = Showable A
  Showable (tele A)    = ⊥
  Showable (rose cs i) = Named cs × All ShowableTele cs

mutual
  tryShowFold : ∀ {I} {cs : Desc I} {{ns : Named cs × All ShowableTele cs}}
              -> ∀ t -> Fold (Rose cs) t -> String
  tryShowFold (ret _)  r = show r
  tryShowFold (pi _ _) f = "CAN'T DO THAT"

  showsExtend : ∀ {I} {cs : Desc I} {i t} {{ns : Named cs × All ShowableTele cs}}
              -> ShowableTele t -> Extend (Rose cs) i t -> List String
  showsExtend {t = ret (ts , _)}  tt     (fs , _) = unmap (λ {t} -> tryShowFold t) fs
  showsExtend {t = pi A B      } (s , t) (x  , e) = show x ∷ showsExtend (t x) e

  show : ∀ {k} {A : Univ k} {{sh : Showable A}} -> ⟦ A ⟧ -> String
  show {A = bot      } {{()}}       _
  show {A = top      }              tt       = "tt"
  show {A = unit     }              triv     = "triv"
  show {A = nat      }              n        = Nat.show n
  show {A = univ k   } {{()}}       _
  show {A = σ A B    } {{s , t}}   (x , y)   =
    parens $ show {{s}} x s++ " , " s++ show {{t x}} y
  show {A = π A B    } {{()}}       f
  show {A = list A   }              xs       =
    parens $ sconcat (intersperse " ∷ " (lmap show xs)) s++ " ∷ []"
  show {A = tele A   } {{()}}       t
  show {A = rose y _ } {{ns , ss}} (node cs) =
    parens $ recAllAny (uncurry λ c st e -> sconcat $ intersperse " " $ c ∷ showsExtend st e)
                       (zipAll (names ns) ss)
                        cs



-- Just copypasted constructors from the appropriate modules.
-- Don't want to change them or the whole encoding for now.

open import Relation.Binary.PropositionalEquality renaming (refl to prefl)

open import OTT.Data.Fin

fin-cs : Desc nat
fin-cs = (pi nat λ n -> ret ([] , suc n)) ∷ (pi nat λ n -> ret (ret n ∷ [] , suc n)) ∷ []

instance
  named-fin : Named fin-cs
  named-fin = record { names = "fzero" ∷ "fsuc" ∷ [] }

test₁ : show (Fin 3 ∋ fsuc (fsuc fzero)) ≡ "(fsuc 2 (fsuc 1 (fzero 0)))"
test₁ = prefl

open import OTT.Data.Vec

vec-cs : Type -> Desc nat
vec-cs A = ret ([] , 0) ∷ (pi nat λ n -> A ⇨ ret (ret n ∷ [] , suc n)) ∷ []

instance
  named-vec : {A : Type} -> Named (vec-cs A)
  named-vec = record { names = "nil" ∷ "cons" ∷ [] }

test₂ : show (Vec (nat & nat) 3 ∋ (7 , 8) ∷ᵥ (9 , 10) ∷ᵥ (11 , 12) ∷ᵥ []ᵥ)
      ≡ "(cons 2 (7 , 8) (cons 1 (9 , 10) (cons 0 (11 , 12) (nil))))"
test₂ = prefl
