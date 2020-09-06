

module Empty where

open import Lib
open import CwF

Empty : ∀ {i Γ} → Ty {i} Γ lzero
Empty = ty (λ _ → ⊥) (λ _ → ⊤)

Empty[] : ∀ {i j Γ Δ}(σ : Sub {i} Γ {j} Δ) → Empty [ σ ]T ≡ Empty
Empty[] σ = refl

EmptyElim : ∀ {i j Γ}(A : Ty {i} Γ j) → Tm Γ Empty → Tm Γ A
EmptyElim A t = tm (λ γ → ⊥-elim (P t γ)) λ {γ} _ → ⊥-elim (P t γ)

EmptyElim[] : ∀ {i j k Γ Δ}{A : Ty Δ k}{σ : Sub {i} Γ {j} Δ}{t : Tm Δ Empty}
              → EmptyElim A t [ σ ]t ≡ EmptyElim (A [ σ ]T) (t [ σ ]t)
EmptyElim[] {σ = σ} {t} = Tm≡ (λ _ → refl) (λ γ α → ⊥-elim (P t (P σ γ)))
