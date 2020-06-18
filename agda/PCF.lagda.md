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

data _∋_ : Context -> Ty -> Set where
  z : ∀ {Γ τ} -> (τ ∷ Γ) ∋ τ
  s : ∀ {Γ τ σ} -> Γ ∋ τ -> (σ ∷ Γ) ∋ τ 
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
    -> Γ ∋ τ
    -----------
    -> Term Γ τ

  ƛ_ : {Γ : Context}{τ α : Ty}
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
    -> Term (τ ∷ Γ) τ
    -----------------
    -> Term Γ τ

```

```
record Kit (_◆_ : Context -> Ty -> Set) : Set where
  constructor kit
  field
    vr : ∀ {Γ τ} -> Γ ∋ τ -> Γ ◆ τ
    tm : ∀ {Γ τ} -> Γ ◆ τ -> Term Γ τ
    wk : ∀ {Γ τ σ} -> Γ ◆ τ -> (σ ∷ Γ) ◆ τ

lift : ∀ {Γ Δ τ σ}{_◆_ : Context -> Ty -> Set} -> Kit _◆_ -> (∀ {υ} -> Γ ∋ υ -> Δ ◆ υ) -> (σ ∷ Γ) ∋ τ -> (σ ∷ Δ) ◆ τ
lift (kit vr tm wk) μ z = vr z
lift (kit vr tm wk) μ (s v) = wk (μ v)

trav : ∀ {Γ Δ τ}{_◆_ : Context -> Ty -> Set} -> Kit (_◆_) -> (∀ {υ} -> Γ ∋ υ -> Δ ◆ υ) -> Term Γ τ -> Term Δ τ
trav (kit vr tm wk) μ (var x) = tm (μ x)
trav K μ (ƛ t)                = ƛ trav K (lift K μ) t
trav K μ (t $ t₁)             = trav K μ t $ trav K μ t₁
trav K μ tt                   = tt
trav K μ ff                   = tt
trav K μ (k n)                = k n
trav K μ (t +1)               = (trav K μ t) +1
trav K μ (t ∸1)               = trav K μ t ∸1
trav K μ (t ≟0)               = (trav K μ t) ≟0
trav K μ (t ¿ t₁ ⦂ t₂)        = trav K μ t ¿ trav K μ t₁ ⦂ trav K μ t₂
trav K μ (Y t)                = Y trav K (lift K μ) t

rename : ∀ {Γ Δ τ} -> (∀ {υ} -> Γ ∋ υ -> Δ ∋ υ) -> (Term Γ τ -> Term Δ τ)
rename μ = trav (kit (λ x -> x) var s) μ

substitution : ∀ {Γ Δ τ} -> (∀ {υ} -> Γ ∋ υ -> Term Δ υ) -> (Term Γ τ -> Term Δ τ)
substitution μ = trav (kit var (λ x → x) (rename s))μ

_[_] : ∀ {Γ τ σ} -> Term (σ ∷ Γ) τ -> Term Γ σ -> Term Γ τ
_[_] {Γ}{τ}{σ} F A = substitution {σ ∷ Γ}{Γ}{τ} μ F
  where
    μ : ∀ {υ} -> (σ ∷ Γ) ∋ υ -> Term Γ υ
    μ z = A
    μ (s x) = var x
```



