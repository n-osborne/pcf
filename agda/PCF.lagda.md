# Programming Language for Computable Functions

The idea is to build a formalisation of PCF based on:

- Dana Scott, *A type-theoretical alternative to ISWIM, CUCH, OWHY*, Theoretical Computer Science 121 (1993) 411-440
- Gordon Plotkin, *LCF Considered as a Programming Language*, Theoretical Computer Science 5 &1977) 223-255

I also use programming technique from

- [Programming Language Foundations in Agda](https://plfa.github.io/)
- Thorsten Altenkrich and Bernhard Reus, *Monadic presentations of lambda terms using generalized inductive types*, Lecture Notes in Computer Science, October 1999


```agda

module PCF where

open import Data.Nat using (zero; suc) renaming (ℕ to Nat)
open import Data.List using (List; _∷_; [])

```
Firstly, we need to define the types. There are two ground types, namely the
type ι of individuals that we are going to interpret as naturals and the type
o of booleans. Then, we also have a function type constructor.

```agda

data Ty : Set where
  ι : Ty
  o : Ty
  _⇒_ : Ty -> Ty -> Ty

```

As we are going to use De Bruijn indexes, so a typing context is just
a liste of types.  We then will use the membership proof to identify a
variable in a context.

```agda

Context = List Ty

data _∈_ : Ty -> Context -> Set where
  hd : {Γ : Context}{τ : Ty} -> τ ∈ (τ ∷ Γ)
  tl : {Γ : Context}{τ σ : Ty} -> τ ∈ Γ -> τ ∈ (σ ∷ Γ)

```

A term depends on the context in which it is valid and its type.
We want to have:

- variables
- abstraction
- application
- literal (booleans: tt ff, and naturals constants: k_)
- increment and decrement a natural
- test whether a natural is equal to zero
- conditinal branchement (Scott and Plotkin use ⊃, but we prefer the ternary operator) 
- recursive functions (Y combinator in PCF)

```agda

data Term : Context -> Ty -> Set where

  var : {Γ : Context}{τ : Ty}
    -> τ ∈ Γ
    -----------
    -> Term Γ τ

  ƛ_∙_ : {Γ : Context}{τ : Ty}
    -> (α : Ty)
    -> Term (α ∷ Γ) τ
    -----------------------
    -> Term Γ (α ⇒ τ) 

  _$_ : {Γ : Context}{τ α : Ty}
    -> Term Γ (α ⇒ τ)
    -> Term Γ α
    -----------------
    -> Term Γ τ

  tt ff : {Γ : Context}
    -----------
    -> Term Γ o

  k_ : {Γ : Context}
    -> Nat
    -----------
    -> Term Γ ι

  _+1 _∸1 : {Γ : Context}
    -> Term Γ ι
    -----------
    -> Term Γ ι

  _≟0 : {Γ : Context}
    -> Term Γ ι
    -----------
    -> Term Γ o

  _¿_⦂_ : {Γ : Context}{τ : Ty}
    -> Term Γ o
    -> Term Γ τ
    -> Term Γ τ
    -----------
    -> Term Γ τ
    
  Y_ : {Γ : Context}{τ : Ty}
    -> Term Γ (τ ⇒ τ)
    -----------------
    -> Term Γ τ

```

Comes the substitution definition. In order to express the semantic of
PCF, we have to be able to define the subsitution operation of a
variable in a term.

According to *plfa* this formalisation of renaming and substitution
is due to McBride, but we are still unable to identify a reference.

As a substitution make a variable disapear (the one that is replaced
by a term), the context of the term on which the substitution operates
is changed. This operation of changing the context is called `renaming`

We'll need to have an auxilary functions that extends a context, that
is, given a map from a membership proof in a context Γ to a membership
proof, for the same type, in a context Δ, the `extend` function
compute a the map from the membership proof of a type in the context Γ
extended with another type to the membership proof of the same type in
the context Δ extended in the same way. This auxiliary function will
be used when we cross a binder (in our case, when we enter in the body
of a lambda abstraction).

```agda

extend : ∀ {Γ Δ} -> (∀ {τ} -> τ ∈ Γ -> τ ∈ Δ) -> ∀ {τ σ} -> τ ∈ (σ ∷ Γ) -> τ ∈ (σ ∷ Δ)
extend m hd = hd
extend m (tl prf) = tl (m prf)

```

Then we can define renaming. Given a map as above and a Term of type τ
in context Γ, the `rename` function computes the equivalent term in
the context Δ. Concretly, to rename a term means to apply the given
map to the variable identifier (which are membership proof) and to
extend the map when we cross a binder, so we won't rename it.

```agda

rename : ∀ {Γ Δ} -> (∀ {τ} -> τ ∈ Γ -> τ ∈ Δ) -> ∀ {τ} -> Term Γ τ -> Term Δ τ
rename m (var x) = var (m x)
rename m (ƛ α ∙ t) = ƛ α ∙ rename (extend m) t
rename m (f $ a) = rename m f $ rename m a
rename m tt = tt
rename m ff = tt
rename m (k x) = k x
rename m (t +1) = (rename m t) +1
rename m (t ∸1) = (rename m t) ∸1
rename m (t ≟0) = (rename m t) ≟0
rename m (t ¿ t₁ ⦂ t₂) = rename m t ¿ rename m t₁ ⦂ rename m t₂
rename m (Y t) = Y rename m t

```

In order to implement substitution, we'll also need to extend a map,
but this time, the map is between a proof of membership in a context
to a term in another context. The proof of membership in the context Γ
is the identifier of the variable in the context Γ (the context of the
term on which the substitution is operated). We want to replace the
occurrences of a variable by a term, but the context of the term is
not necessarily the same as the one of the initial term. So we need to
be able to map the proof of membership in a context Γ to a Term valid
in a context Δ.

Then, substitution is really simililar to renaming:

- in case of a var, we apply the map to the membership proof to compute the term
- in case of a lambda abstraction, we call substitution on the body with an extended map
- in the other cases, we proceed recursively

```agda

extends : ∀ {Γ Δ} -> (∀ {τ} -> τ ∈ Γ -> Term Δ τ) -> ∀ {τ σ} -> τ ∈ (σ ∷ Γ) -> Term (σ ∷ Δ) τ
extends m hd = var hd
extends m (tl prf) = rename tl (m prf)

substitution : ∀ {Γ Δ} -> (∀ {τ} -> τ ∈ Γ -> Term Δ τ) -> ∀ {τ} -> Term Γ τ -> Term Δ τ
substitution m (var x) = m x
substitution m (ƛ α ∙ t) = ƛ α ∙ substitution (extends m) t
substitution m (t $ t₁) = substitution m t $ substitution m t₁
substitution m tt = tt
substitution m ff = tt
substitution m (k n) = k n
substitution m (t +1) = (substitution m t) +1
substitution m (t ∸1) = (substitution m t) ∸1
substitution m (t ≟0) = (substitution m t) ≟0
substitution m (t ¿ t₁ ⦂ t₂) = substitution m t ¿ substitution m t₁ ⦂ substitution m t₂
substitution m (Y t) = Y substitution m t

```

Now we can specialize `substitution`. The final function takes the
body of a lambda abstraction (a term valid in the context σ ∷ Γ, σ
being the type of the binder) and a term of type σ valid in Γ. The
idea is to call `substitution` on the body of the lambda abstraction
with the map m defined to replace occurences of the variable bound to
this abstraction by the given term. `substitution` will take care of
extending the map whe crossing internal binder.

```agda

_[_] : ∀ {Γ τ σ} -> Term (σ ∷ Γ) τ -> Term Γ σ -> Term Γ τ
_[_] {Γ}{τ}{σ} N M = substitution {σ ∷ Γ} {Γ} m {τ} N
  where
    m : ∀ {τ} -> τ ∈ (σ ∷ Γ) -> Term Γ τ
    m hd = M
    m (tl x) = var x

```
