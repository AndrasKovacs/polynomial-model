
{-# OPTIONS --type-in-type #-}

module Empty where

open import Lib
open import CwF

Empty : ∀ {Γ} → Ty Γ
Empty {Γ} = ty (λ _ → ⊥) (λ _ → ⊤)

Empty[] : ∀ {Γ Δ}(σ : Sub Γ Δ) → Empty [ σ ]T ≡ Empty
Empty[] σ = refl

EmptyElim : ∀ {Γ}(A : Ty Γ) → Tm Γ Empty → Tm Γ A
EmptyElim {Γ} A t = tm (λ γ → ⊥-elim (P t γ)) λ {γ} _ → ⊥-elim (P t γ)

EmptyElim[] : ∀ {Γ Δ A}{σ : Sub Γ Δ}{t : Tm Δ Empty}
              → EmptyElim A t [ σ ]t ≡ EmptyElim (A [ σ ]T) (t [ σ ]t)
EmptyElim[] {Γ} {Δ} {A} {σ} {t} = Tm≡ (λ _ → refl) (λ γ α → ⊥-elim (P t (P σ γ)))
