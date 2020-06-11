module PCF where

open import Data.Nat using (_+_) renaming (ℕ to Nat; _∸_ to _-_)
open import Data.List using (List; _∷_; [])

data Ty : Set where
  two : Ty
  nat : Ty
  fun : Ty -> Ty -> Ty

Context = List Ty

data _∈_ : Ty -> Context -> Set where
  hd : {Γ : Context}{τ : Ty} -> τ ∈ (τ ∷ Γ)
  tl : {Γ : Context}{τ σ : Ty} -> τ ∈ Γ -> τ ∈ (σ ∷ Γ)
  
data Term : Context -> Ty -> Set where
  var : {Γ : Context}{τ : Ty} -> τ ∈ Γ -> Term Γ τ
  abs : {Γ : Context}{τ : Ty}(α : Ty) -> (t : Term Γ τ) -> Term (α ∷ Γ) (fun α τ) 
  app : {Γ : Context}{τ : Ty}(α : Ty) -> (f : Term Γ (fun α τ)) -> (a : Term Γ α) -> Term Γ τ
  top : {Γ : Context} -> Term Γ two
  bot : {Γ : Context} -> Term Γ two
  nat : {Γ : Context} -> Nat -> Term Γ nat
  add : {Γ : Context} -> Term Γ nat -> Term Γ nat -> Term Γ nat
  min : {Γ : Context} -> Term Γ nat -> Term Γ nat -> Term Γ nat
  beq : {Γ : Context} ->  Term Γ nat -> Term Γ nat -> Term Γ two
  test_then_else_ : {Γ : Context}{τ : Ty} -> Term Γ two -> Term Γ τ -> Term Γ τ
  fix : {Γ : Context}{τ : Ty} -> Term (τ ∷ Γ) τ -> Term Γ τ 

  

