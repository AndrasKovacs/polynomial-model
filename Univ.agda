
module Univ where

open import Lib
open import CwF

U : ∀ {i Γ} j → Ty {i} Γ (lsuc j)
U j = ty (λ _ → Con j) (λ _ → ⊥)

El : ∀ {i j Γ} → Tm {i} Γ (U j) → Ty Γ j
El A = ty (λ γ → P (P A γ)) (λ {γ} → R (P A γ))

El[] : ∀ {i j k Γ Δ}{σ : Sub {i}Γ{j} Δ}{a : Tm Δ (U k)} → (El a) [ σ ]T ≡ El (a [ σ ]t)
El[] = refl

c : ∀ {i j Γ} → Ty {i} Γ j → Tm Γ (U j)
c A = tm (λ γ → con (P A γ) (R A)) ⊥-elim

cEl : ∀ {i j Γ a} → c (El {i}{j}{Γ} a) ≡ a
cEl = Tm≡ (λ _ → refl) (λ _ ())

Elc : ∀ {i j Γ A} → El {i}{j}{Γ} (c A) ≡ A
Elc = refl
