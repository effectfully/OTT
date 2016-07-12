# OTT

It's an implementation of Observational Type Theory as an Agda library. The universe contains `⊤`, `⊥`, natural numbers, Σ- and Π-types, impredicative `Prop` that lies in `Type₀`, infinite non-cumulative hierarchy `Type₀ : Type₁ : Type₂ : ...` and tools for generic programming: descriptions, their fixed points and finite enumerations.

## Details

(The readme is a bit old: a `Level` now fully reifies the corresponding `MetaLevel` and there is also a [generic machinery](https://github.com/effectfully/OTT/blob/master/Function/Elim.agda) which allows to derive intensional-type-theory-like eliminators which is annoying to do by hand when a data type is indexed so you need to explicitly use `J`)

There are two main kinds of universe levels (there is also yet another one, but it's not important): metatheory levels (the usual `Level` type renamed to `MetaLevel`) and target theory levels, indexed by metalevels:

```
data Level : MetaLevel -> Set where
  lzero : Level lzeroₘ
  lsuc  : ∀ a -> Level (lsucₘ a)
```

This is needed, because `Prop` is represented as `Univ lzero` and `Type a` is represented as `Univ (lsuc a)`, so we need to be able to pattern match on `α` in `Univ α` to decide whether a type is a proposition or a set (because propositions and sets are often handled differently), but metalevels are parametric and hence can't be pattern matched on.

The form of descriptions used here is described at the bottom (the `CompProp` module) of [9]. However in this development descriptions support full universe polymorphism (which makes them too down-to-earth to be able to perform levitation (not in a straightforward way at least), but that doesn't seem to be a problem). When defining a description we need to make sure that each `π` binds a variable which type lies in a smaller or the same universe than the type of the whole description. I.e. something like

`π : ∀ {α} -> α ≤ β -> (A : Univ α) -> (⟦ A ⟧ -> Desc I β) -> Desc I β`

If levels would be just natural numbers, that would work, however forcing a user to write down such boring and verbose proofs (though, we could probably use a solver with some reflection) would be too obtrusive. But `α ≤ β` can be equally written as `α ⊔ β ≡ β` and Agda has a built-in solver for universe levels, so here is the definition of `Desc`:

```
data Desc {i b} (I : Type i) (β : Level b) : Set where
  var : ⟦ I ⟧ -> Desc I β
  π   : ∀ {a} {α : Level a} .{{_ : a ⊔ₘ b ≡ b}}
      -> (A : Univ α) -> (⟦ A ⟧ -> Desc I β) -> Desc I β
  _⊛_ : Desc I β -> Desc I β -> Desc I β
```

It's possible to avoid the use of instance arguments:

```
data UDesc {i o} (I : Type i) (ω : Level o) : (a : MetaLevel) -> Set where
  var[_] : ∀ {a} -> .(o ≡ a) -> ⟦ I ⟧ -> UDesc I ω a
  π[_]   : ∀ {a b} {α : Level a}
         -> .(a ⊔ₘ o ≡ b) -> (A : Univ α) -> (⟦ A ⟧ -> UDesc I ω b) -> UDesc I ω b
  _⊛_    : ∀ {a} -> UDesc I ω a -> UDesc I ω a -> UDesc I ω a

Desc : ∀ {a i} -> Type i -> Level a -> Set
Desc {a} I α = UDesc I α a
```

Here `ω` is the final level and `a` is the inferred level. `Desc` requires these levels to be equal, thereby forcing unification. However this is more complicated and verbose, so I chose the first version.

We have two notions of type equality: types can be equal either weakly

```
_≈_ : ∀ {a b} {α : Level a} {β : Level b} -> Univ α -> Univ β -> Prop
_≈_ {α = lzero } {lzero } A₁ A₂ = A₁ ⇒ A₂ & A₂ ⇒ A₁
_≈_ {α = lsuc _} {lsuc _} A₁ A₂ = A₁ ≃ A₂
_≈_                       _  _  = bot
```

or strictly

```
bot     ≃ bot     = top
top     ≃ top     = top
σ A₁ B₁ ≃ σ A₂ B₂ = A₁ ≈ A₂ & B₁ ≅ B₂
π A₁ B₁ ≃ π A₂ B₂ = A₂ ≈ A₁ & π A₁ λ x₁ -> π A₂ λ x₂ -> x₂ ≅ x₁ ⇒ B₁ x₁ ≈ B₂ x₂
...
```

Weak equality for propositions is isomorphism, weak equality for sets is strict equality.

In the same way there are two equalities for descriptions, since a description can lie in `Prop` — this happens when a description contains only propositions and inductive occurrences.

The straightforward strict equality:

```
_≅ᵈ_ : ∀ {i₁ i₂ a₁ a₂} {α₁ : Level a₁} {α₂ : Level a₂} {I₁ : Type i₁} {I₂ : Type i₂}
     -> Desc I₁ α₁ -> Desc I₂ α₂ -> Prop
var i₁    ≅ᵈ var i₂    = i₁ ≅ i₂
π A₁ D₁   ≅ᵈ π A₂ D₂   = A₁ ≈ A₂ & D₁ ≅ D₂
(D₁ ⊛ E₁) ≅ᵈ (D₂ ⊛ E₂) = D₁ ≅ᵈ D₂ & E₁ ≅ᵈ E₂
_         ≅ᵈ _         = bot
```

Described propositions are equal if their fixed points (propositions themselves) are isomorphic:

```
_≊ᵈ_ : ∀ {i₁ i₂ a₁ a₂} {α₁ : Level a₁} {α₂ : Level a₂} {I₁ : Type i₁} {I₂ : Type i₂}
     -> Desc I₁ α₁ -> Desc I₂ α₂ -> Prop
_≊ᵈ_ {α₁ = lzero } {lzero } D₁ D₂ = imu D₁ ≅ imu D₂
_≊ᵈ_ {α₁ = lsuc _} {lsuc _} D₁ D₂ = D₁ ≅ᵈ D₂
_≊ᵈ_                        _  _  = bot
```

Correspondingly, there are two `coerce`s: a one which requires weak equality

```
coerce : ∀ {a b} {α : Level a} {β : Level b} {A : Univ α} {B : Univ β} -> ⟦ A ≈ B ⇒ A ⇒ B ⟧
coerce {α = lzero } {lzero } (f , _) = f
coerce {α = lsuc _} {lsuc _}  q      = coerce′ q
coerce {α = lzero } {lsuc _}  ()
coerce {α = lsuc _} {lzero }  ()
```

and a one which requires strict

```
coerce′ : ∀ {a b} {α : Level a} {β : Level b} {A : Univ α} {B : Univ β} -> ⟦ A ≃ B ⇒ A ⇒ B ⟧
coerce′ {A = bot     } {bot     } q ()
coerce′ {A = top     } {top     } q tt = tt
coerce′ {A = σ A₁ B₁ } {σ A₂ B₂ } q p  = let q₁ , q₂ = q ; x , y = p in
  coerce q₁ x , coerce (q₂ x (coerce q₁ x) (coherence q₁ x)) y
coerce′ {A = π A₁ B₁ } {π A₂ B₂ } q f  = let q₁ , q₂ = q in
  λ x -> coerce (q₂ (coerce q₁ x) x (coherence q₁ x)) (f (coerce q₁ x))
...
```

`desc` allows to encode inductive data types (including inductive families) in the target theory. `coerce` computes under constructors of data types (see the "5. Full OTT" section of [1] for how this works). Each inductive family has at least two eliminators: one classical and one "up to propositional equality". An example from the `OTT.Data.Fin` module:

```
elimFinₑ : ∀ {n π}
         -> (P : ∀ {n} -> Fin n -> Set π)
         -> (∀ {n m} {i : Fin n} -> (q : ⟦ suc n ≅ m ⟧) -> P i -> P {m} (fsucₑ q i))
         -> (∀ {n m} -> (q : ⟦ suc n ≅ m ⟧) -> P {m} (fzeroₑ q))
         -> (i : Fin n)
         -> P i
elimFinₑ P f x (fzeroₑ q)  = x q
elimFinₑ P f x (fsucₑ q i) = f q (elimFinₑ P f x i)
```

`elimFinₑ` is an "up to propositional equality" eliminator. The thing here is that `elimFinₑ` doesn't contain any coercions at all, so its "non-dependent" computational behaviour is the same as the corresponding behaviour of an eliminator in an intensional type theory. It even gives you slightly more:

```
elimFin′ : ∀ {n π}
         -> (P : ∀ n -> Set π)
         -> (∀ {n} {i : Fin n} -> P (fromFin i) -> P (suc (fromFin i)))
         -> P 0
         -> (i : Fin n)
         -> P (fromFin i)
elimFin′ P f x = elimFinₑ (P ∘ fromFin) (λ {n m i} _ -> f {i = i}) (const x)
```

`elimFin′` doesn't mention `coerce` as well.

We can recover the usual eliminator with the help from our old friend:

```
J : ∀ {a b} {α : Level a} {β : Level b} {A : Univ α} {x y : ⟦ A ⟧}
  -> (B : (y : ⟦ A ⟧) -> ⟦ x ≅ y ⟧ -> Univ β)
  -> ⟦ B _ (refl x) ⟧
  -> (q : ⟦ x ≅ y ⟧)
  -> ⟦ B _ q ⟧
J {x = x} B z q = subst₂ B q (huip x q) z

elimFin : ∀ {n k}
        -> (P : ∀ {n} -> Fin n -> Univ k)
        -> (∀ {n} {i : Fin n} -> ⟦ P i ⇒ P (fsuc i) ⟧)
        -> (∀ {n} -> ⟦ P {suc n} fzero ⟧)
        -> (i : Fin n)
        -> ⟦ P i ⟧
elimFin P f x = elimFinₑ (⟦_⟧ ∘ P)
  (λ q r -> J (λ m q -> P {m} (fsucₑ q _)) (f r) q)
  (J (λ m q -> P {m} (fzeroₑ q)) x)
```

`subst₂` is defined in terms of `coerce`, so it computes under constructors of data types too, hence classical eliminators have pretty good computational behaviour too.

A simple test:

```
postulate
  n m : ℕ

test : ⟦ fromFin ((Fin (3 + n) ∋ fsuc (fsuc fzero)) +ᶠ (Fin (2 + m) ∋ fsuc fzero)) ≅ 3 ⟧
test = tt
```

`n` and `m` are stuck, but the expression reduces properly regardless of whether `_+ᶠ_` is defined in terms of `elimFin′` or `elimFin`.

Eliminators for inductive data types (not families) are the usual intensional eliminators, e.g.

```
[_,_] : ∀ {a b π} {α : Level a} {β : Level b} {A : Univ α} {B : Univ β} {P : A ⊎ B -> Set π}
      -> (∀ x -> P (inj₁ x)) -> (∀ y -> P (inj₂ y)) -> ∀ s -> P s
[ f , g ] (inj₁ x) = f x
[ f , g ] (inj₂ y) = g y

elimW : ∀ {a b π} {α : Level a} {β : Level b} {A : Univ α} {B : ⟦ A ⟧ -> Univ β}
      -> (P : W A B -> Set π)
      -> (∀ {x} {g : ⟦ B x ⟧ -> W A B} -> (∀ y -> P (g y)) -> P (sup x g))
      -> ∀ w
      -> P w
elimW P h (sup x g) = h (λ y -> elimW P h (g y))
```

An example of generic programming can be found in the `Property/Eq.agda` module which defines this operator:

`_≟_ : ∀ {a} {α : Level a} {A : Univ α} {{eqA : Eq A}} -> (x y : ⟦ A ⟧) -> Dec (x ≡ y)`

It can handle numbers, finite sets, sums, products, lists and many other data types. An example:

```
ns : List (list nat ⊕ σ nat fin)
ns = inj₁ (1 ∷ 4 ∷ []) ∷ inj₂ (3 , fsuc fzero) ∷ inj₂ (2 , fzero) ∷ []

test : (ns ≟ ns) ≡ yes prefl
test = prefl
```

There is [an alternative encoding](https://github.com/effectfully/random-stuff/blob/master/Desc/IRDesc.agda) which is a modified version of [7]. It's more powerful (it's able to express induction-recursion), but also significantly more complicated: data types must be defined mutually with coercions, which results in a giant mutual block. I didn't try to define equality and coercions for descriptions, but I suspect it's much harder than how it's now. I'll go with the current simple app

## Not implemented

- Definitional proof irrelevance.

- Erasion of stuck coercions between definitionally equal types (that's not my fault, Agda just doesn't have an available definitional equality checker) (note that we have proper eliminators without this tool unlike in OTT with W-types (and they are still improper, see [4])).

- Codata (is it simply the coinductive counterpart of `μ`?).

- Quotients. Or maybe we can implement even quotient inductive types ([10])?

## A final remark

Note that it's a library and not a formalization, since termination and positivity checkers are disabled. There are also several postulates (as well as in the original OTT), but nothing unexpected:

```
postulate
  refl      : ∀ {a} {α : Level a} {A : Univ α} -> (x : ⟦ A ⟧) -> ⟦ x ≅ x ⟧
  coherence : ∀ {a b} {α : Level a} {β : Level b} {A : Univ α} {B : Univ β}
            -> (q : ⟦ A ≈ B ⟧) -> (x : ⟦ A ⟧) -> ⟦ x ≅ coerce q x ⟧
  cong-≅z   : ∀ {a b c} {α : Level a} {β : Level b} {γ : Level c}
                {A : Univ α} {B : Univ β} {C : Univ γ}
            -> (x : ⟦ A ⟧) {y : ⟦ B ⟧} {z : ⟦ C ⟧} -> (q : ⟦ x ≅ y ⟧) -> ⟦ (x ≅ z) ≈ (y ≅ z)⟧
  huip      : ∀ {a b} {α : Level a} {β : Level b} {A : Univ α} {B : Univ β}
            -> (x : ⟦ A ⟧) {y : ⟦ B ⟧} -> (q : ⟦ x ≅ y ⟧) -> ⟦ refl x ≅ q ⟧
```

## References

[1] ["Towards Observational Type Theory"](http://strictlypositive.org/ott.pdf), Thorsten Altenkirch and Conor McBride

[2] ["Observational Equality, Now!"](http://www.cs.nott.ac.uk/~psztxa/publ/obseqnow.pdf), Thorsten Altenkirch, Conor McBride, Wouter Swierstra

[3] ["Hier Soir, an OTT Hierarchy"](http://mazzo.li/epilogue/index.html%3Fp=1098.html), Conor McBride

[4] ["W-types: good news and bad news"](http://mazzo.li/epilogue/index.html%3Fp=324.html), Conor McBride

[5] ["On Universes in Type Theory"](http://citeseerx.ist.psu.edu/viewdoc/download?doi=10.1.1.221.1318&rep=rep1&type=pdf), Erik Palmgren

[6] ["Modeling Elimination of Described Types"](http://spire-lang.org/blog/2014/01/15/modeling-elimination-of-described-types/), Larry Diehl

[7] ["Inductive-Recursive Descriptions"](http://spire-lang.org/blog/2014/08/04/inductive-recursive-descriptions/), Larry Diehl

[8] ["The Gengtle Art of Levitation"](https://jmchapman.github.io/papers/levitation.pdf), James Chapman, Pierre-Évariste Dagand, Conor McBride, Peter Morris

[9] ["Descriptions"](http://effectfully.blogspot.ru/2016/04/descriptions.html)

[10] ["Type Theory in Type Theory using Quotient Inductive Types"](http://www.cs.nott.ac.uk/~psztxa/publ/tt-in-tt.pdf), Thorsten Altenkirch, Ambrus Kaposi.
