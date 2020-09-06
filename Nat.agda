{-# OPTIONS --type-in-type #-}

module Nat where

open import Lib
open import CwF

Nat : ∀ {Γ} → Ty Γ
Nat = ty (λ _ → ℕ) (λ _ → ⊥)

Nat[] : ∀ {Γ Δ}{σ : Sub Γ Δ} → Nat [ σ ]T ≡ Nat
Nat[] = refl

Zero : ∀ {Γ} → Tm Γ Nat
Zero = tm (λ _ → zero) (λ ())

Zero[] : ∀ {Γ Δ}{σ : Sub Γ Δ} → Zero [ σ ]t ≡ Zero
Zero[] = Tm≡ (λ _ → refl) (λ _ → λ ())

Suc : ∀ {Γ} → Tm Γ Nat → Tm Γ Nat
Suc t = tm (λ γ → suc (P t γ)) (λ ())

Suc[] : ∀ {Γ Δ}{σ : Sub Γ Δ}{n} → (Suc n) [ σ ]t ≡ Suc (n [ σ ]t)
Suc[] = Tm≡ (λ _ → refl) (λ _ → λ ())

NatElim :
  ∀ {Γ}(Pr : Ty (Γ ▶ Nat))
  → Tm Γ (Pr [ < Zero > ]T)                   -- Pr zero
  → Tm (Γ ▶ Nat ▶ Pr) (Pr [ wk² ,ₛ Suc v₁ ]T) -- (∀ n → Pr n → Pr (suc n))
  → (n : Tm Γ Nat)
  → Tm Γ (Pr [ < n > ]T)
P (NatElim {Γ} Pr PZ PS n) γ =
  natElim (λ n → P Pr (γ , n)) (P PZ γ) (λ n pn → P PS ((γ , n) , pn)) (P n γ)
R (NatElim {Γ} Pr PZ PS n) {γ} =
  natElim (λ n → R Pr (natElim (λ n → P Pr (γ , n)) (P PZ γ) (λ n pn → P PS ((γ , n) , pn)) n)
               → R Γ γ)
          (R PZ)
          (λ n hyp RPr → case ⊎⊥ hyp (R PS RPr))
          (P n γ)

Zeroβ : ∀ {Γ Pr PZ PS} →  NatElim {Γ} Pr PZ PS Zero ≡ PZ
Zeroβ = refl

Sucβ :
  ∀ {Γ Pr PZ PS n}
  → NatElim {Γ} Pr PZ PS (Suc n) ≡ PS [ id ,ₛ n ,ₛ NatElim Pr PZ PS n ]t
Sucβ {Γ} {Pr} {PZ} {PS} {n} = Tm≡ (λ _ → refl) R≡ where
  R≡ : _
  R≡ γ α with R PS α
  ... | inj₁ (inj₁ _) = refl
  ... | inj₂ y = refl

NatElim[] :
  ∀ {Γ Δ Pr PZ PS n}{σ : Sub Γ Δ}
  → NatElim {Δ} Pr PZ PS n [ σ ]t
  ≡ NatElim {Γ} (Pr [ σ ^ Nat ]T) (PZ [ σ ]t) (PS [ σ ^ Nat ^ Pr ]t) (n [ σ ]t)
NatElim[] {Γ} {Δ} {Pr} {PZ} {PS} {n} {σ} = Tm≡ (λ _ → refl) R≡ where

  -- Sorry. I practice the ancient art of pasting block-formatted
  -- induction motives into Agda
  R≡ : _
  R≡ γ α = natElim
    (λ pnpσγ → ∀ α →
        R σ (natElim (λ n₁ → R Pr (natElim (λ n₂ → P Pr (P σ γ , n₂)) (P
        PZ (P σ γ)) (λ n₂ pn → P PS ((P σ γ , n₂) , pn)) n₁) → R Δ (P σ γ)) (R PZ)
        (λ n₁ hyp RPr → case ⊎⊥ hyp (R PS RPr)) (pnpσγ) α) ≡ natElim (λ n₁ → R Pr
        (natElim (λ n₂ → P Pr (P σ γ , n₂)) (P PZ (P σ γ)) (λ n₂ pn → P PS ((P σ γ
        , n₂) , pn)) n₁) → R Γ γ) (λ α* → R σ (R PZ α*)) (λ n₁ hyp RPr → case ⊎⊥
        hyp (case (λ σ* → inj₁ (case (λ σ*₁ → inj₁ (R σ σ*₁)) (λ α* → inj₂ α*)
        σ*)) (λ α* → inj₂ α*) (R PS RPr))) (pnpσγ) α)
    (λ _ → refl)
    (λ n hyp α →
        ⊎-elim (λ RPSα →
                  R σ (case ⊎⊥ (natElim (λ n₂ → R Pr (natElim (λ n₃ → P Pr (P σ γ , n₃))
                  (P PZ (P σ γ)) (λ n₃ pn → P PS ((P σ γ , n₃) , pn)) n₂) → R Δ (P σ γ)) (R
                  PZ) (λ n₂ hyp₁ RPr → case ⊎⊥ hyp₁ (R PS RPr)) n) (RPSα)) ≡ case ⊎⊥
                  (natElim (λ n₂ → R Pr (natElim (λ n₃ → P Pr (P σ γ , n₃)) (P PZ (P σ γ))
                  (λ n₃ pn → P PS ((P σ γ , n₃) , pn)) n₂) → R Γ γ) (λ α* → R σ (R PZ α*))
                  (λ n₂ hyp₁ RPr → case ⊎⊥ hyp₁ (case (λ σ* → inj₁ (case (λ σ*₁ → inj₁ (R σ
                  σ*₁)) (λ α* → inj₂ α*) σ*)) (λ α* → inj₂ α*) (R PS RPr))) n) (case (λ σ* →
                  inj₁ (case (λ σ*₁ → inj₁ (R σ σ*₁)) (λ α* → inj₂ α*) σ*)) (λ α* → inj₂ α*)
                  (RPSα)))
                (λ {(inj₁ _) → refl})
                (hyp)
                (R PS α))
    (P n (P σ γ))
    α
