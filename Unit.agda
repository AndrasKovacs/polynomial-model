
{-# OPTIONS --type-in-type #-}

module Unit where

open import Lib
open import CwF

Unit : ∀ {Γ} → Ty Γ
Unit = ty (λ _ → ⊤) (λ _ → ⊥)

Unit[] : ∀ {Γ Δ}{σ : Sub Γ Δ} → Unit {Δ} [ σ ]T ≡ Unit
Unit[] = refl

Tt : ∀ {Γ} → Tm Γ Unit
Tt = tm (λ γ → tt) (λ ())

Tt[] : ∀ {Γ Δ}{σ : Sub Γ Δ} → Tt [ σ ]t ≡ Tt
Tt[] {Γ} {Δ} {σ} = Tm≡ (λ _ → refl) (λ _ → λ ())

Unitη : ∀ {Γ}{t : Tm Γ Unit} → t ≡ Tt
Unitη {Γ} {t} = Tm≡ (λ _ → refl) (λ _ → λ ())
