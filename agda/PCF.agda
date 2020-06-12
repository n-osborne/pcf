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

  ⦅_⦆_ : {Γ : Context}{τ : Ty}(α : Ty)
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


  

