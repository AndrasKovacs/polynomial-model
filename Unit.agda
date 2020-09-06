
module Unit where

open import Lib
open import CwF

Unit : ∀ {i Γ} → Ty {i} Γ lzero
Unit = ty (λ _ → ⊤) (λ _ → ⊥)

Unit[] : ∀ {i j Γ Δ}{σ : Sub {i}Γ{j} Δ} → Unit [ σ ]T ≡ Unit
Unit[] = refl

Tt : ∀ {i Γ} → Tm {i} Γ Unit
Tt = tm (λ γ → tt) (λ ())

Tt[] : ∀ {i j Γ Δ}{σ : Sub {i} Γ {j} Δ} → Tt [ σ ]t ≡ Tt
Tt[] {Γ} {Δ} {σ} = Tm≡ (λ _ → refl) (λ _ → λ ())

Unitη : ∀ {i Γ}{t : Tm {i} Γ Unit} → t ≡ Tt
Unitη = Tm≡ (λ _ → refl) (λ _ → λ ())
