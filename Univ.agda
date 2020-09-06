
module Univ where

open import Lib
open import CwF

U : ∀ {i Γ} j → Ty {i} Γ (lsuc j)
U {Γ} j = ty (λ _ → Σ (Set j) λ A → A → Set j) (λ _ → ⊥)

El : ∀ {i j Γ} → Tm {i} Γ (U j) → Ty Γ j
El A = ty (λ γ → ₁ (P A γ)) (λ {γ} α → ₂ (P A γ) α)

El[] : ∀ {i j k Γ Δ}{σ : Sub {i}Γ{j} Δ}{a : Tm Δ (U k)} → (El a) [ σ ]T ≡ El (a [ σ ]t)
El[] = refl

c : ∀ {i j Γ} → Ty {i} Γ j → Tm Γ (U j)
c A = tm (λ γ → (P A γ) , R A) ⊥-elim

cEl : ∀ {i j Γ a} → c (El {i}{j}{Γ} a) ≡ a
cEl {Γ} {a} = Tm≡ (λ _ → refl) (λ _ ())

Elc : ∀ {i j Γ A} → El {i}{j}{Γ} (c A) ≡ A
Elc {Γ} {A} = refl
