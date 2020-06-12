module PCF where

open import Data.Nat using (zero; suc) renaming (ℕ to Nat)
open import Data.List using (List; _∷_; [])

data Ty : Set where
  ι : Ty
  o : Ty
  _⇒_ : Ty -> Ty -> Ty

Context = List Ty

data _∈_ : Ty -> Context -> Set where
  hd : {Γ : Context}{τ : Ty} -> τ ∈ (τ ∷ Γ)
  tl : {Γ : Context}{τ σ : Ty} -> τ ∈ Γ -> τ ∈ (σ ∷ Γ)
  
data Term : Context -> Ty -> Set where

  var : {Γ : Context}{τ : Ty}
    -> τ ∈ Γ
    -----------
    -> Term Γ τ

  ƛ_∙_ : {Γ : Context}{τ : Ty}(α : Ty)
    -> (t : Term (α ∷ Γ) τ)
    -----------------------
    -> Term Γ (α ⇒ τ) 

  ⦅_⦆_ : {Γ : Context}{τ α : Ty}
    -> (f : Term Γ (α ⇒ τ))
    -> (a : Term Γ α)
    -----------------
    -> Term Γ τ

  tt : {Γ : Context}
    -----------
    -> Term Γ o

  ff : {Γ : Context}
    -----------
    -> Term Γ o

  k_ : {Γ : Context}
    -> Nat
    -----------
    -> Term Γ ι

  _+1 : {Γ : Context}
    -> Term Γ ι
    -----------
    -> Term Γ ι

  _∸1 : {Γ : Context}
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

-- substitution inspired by plfa
extend : ∀ {Γ Δ} -> (∀ {τ} -> τ ∈ Γ -> τ ∈ Δ) -> (∀ {τ σ} -> τ ∈ (σ ∷ Γ) -> τ ∈ (σ ∷ Δ))
extend m hd = hd
extend m (tl prf) = tl (m prf)

rename : ∀ {Γ Δ} -> (∀ {τ} -> τ ∈ Γ -> τ ∈ Δ) -> (∀ {τ} -> Term Γ τ -> Term Δ τ)
rename m (var x) = var (m x)
rename m (ƛ α ∙ t) = ƛ α ∙ rename (extend m) t
rename m (⦅ f ⦆ a) = ⦅ rename m f ⦆ rename m a
rename m tt = tt
rename m ff = tt
rename m (k x) = k x
rename m (t +1) = (rename m t) +1
rename m (t ∸1) = (rename m t) ∸1
rename m (t ≟0) = (rename m t) ≟0
rename m (t ¿ t₁ ⦂ t₂) = rename m t ¿ rename m t₁ ⦂ rename m t₂
rename m (Y t) = Y rename m t

extends : ∀ {Γ Δ} -> (∀ {τ} -> τ ∈ Γ -> Term Δ τ) -> (∀ {τ σ} -> τ ∈ (σ ∷ Γ) -> Term (σ ∷ Δ) τ)
extends m hd = var hd
extends m (tl prf) = rename tl (m prf)

substitution : ∀ {Γ Δ} -> (∀ {τ} -> τ ∈ Γ -> Term Δ τ) -> (∀ {τ} -> Term Γ τ -> Term Δ τ)
substitution m (var x) = m x
substitution m (ƛ α ∙ t) = ƛ α ∙ substitution (extends m) t
substitution m (⦅ t ⦆ t₁) = ⦅ substitution m t ⦆ substitution m t₁
substitution m tt = tt
substitution m ff = tt
substitution m (k x) = k x
substitution m (t +1) = substitution m t
substitution m (t ∸1) = substitution m t
substitution m (t ≟0) = tt
substitution m (t ¿ t₁ ⦂ t₂) = substitution m t₂
substitution m (Y t) = Y substitution m t

_[_] : ∀ {Γ τ σ} -> Term (σ ∷ Γ) τ -> Term Γ σ -> Term Γ τ
_[_] {Γ}{τ}{σ} N M = substitution {σ ∷ Γ} {Γ} m {τ} N
  where
    m : ∀ {τ} -> τ ∈ (σ ∷ Γ) -> Term Γ τ
    m hd = M
    m (tl x) = var x
