# OTT

It's an implementation of Observational Type Theory as an Agda library. The universe contains `⊤`, `⊥`, natural numbers, Σ- and Π-types, impredicative `Prop` that lies in `Type₀`, infinite non-cumulative hierarchy `Type₀ : Type₁ : Type₂ : ...` and tools for generic programming: descriptions, their fixed points and finite enumerations.

## Details

There are two main kinds of universe levels (there is also yet another one, but it's not important): metatheory levels (the usual `Level` type renamed to `MetaLevel`) and target theory levels, indexed by metalevels:

```
data Level : MetaLevel -> Set where
  lzero : Level lzeroₘ
  lsuc  : ∀ a -> Level (lsucₘ a)
```

This is needed, because `Prop` is represented as `Univ lzero` and `Type a` is represented as `Univ (lsuc a)`, so we need to be able to pattern match on `α` in `Univ α` to decide whether a type is a proposition or a set (because propositions and sets are often handled differently), but metalevels are parametric and hence can't be pattern matched on.

The form of descriptions used here is described at the bottom (the `CompProp` module) of [9]. However in this development descriptions support full universe polymorphism (which makes them too down-to-earth to be able to perform levitation (not in a straightforward way at least), but that doesn't seem to be a problem). When defining a description we need to make sure that each `π` binds a variable which type lies in a smaller or the same universe than the type of the whole description. I.e. something like

`π : ∀ {α} -> α ≤ β -> (A : Univ α) -> (⟦ A ⟧ -> Desc I β) -> Desc I β`

If levels would be just natural numbers that would work, however forcing a user to write down such boring and verbose proofs (though, we could probably use a solver with some reflection) would be too obtrusive. But `α ≤ β` can be equally written as `α ⊔ β ≡ β` and Agda has a built-in solver for universe levels, so here is the definition of `Desc`:

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

Here `ω` is the final level and `a` is the inferred level`. `Desc` requires these levels to be equal, thereby forcing unification. However this is more complicated and verbose, so I chose the first version.

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

In the same way there are two equalities for descriptions, since a description can lie in `Prop` — this happens when the description contains only propositions and inductive occurrences.

The straightforward strict equality:

```
_≅ᵈ_ : ∀ {i₁ i₂ a₁ a₂} {α₁ : Level a₁} {α₂ : Level a₂} {I₁ : Type i₁} {I₂ : Type i₂}
     -> Desc I₁ α₁ -> Desc I₂ α₂ -> Prop
var i₁    ≅ᵈ var i₂    = i₁ ≅ i₂
π A₁ D₁   ≅ᵈ π A₂ D₂   = A₁ ≈ A₂ & π A₁ λ x₁ -> π A₂ λ x₂ -> x₁ ≅ x₂ ⇒ D₁ x₁ ≅ᵈ D₂ x₂
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

...

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