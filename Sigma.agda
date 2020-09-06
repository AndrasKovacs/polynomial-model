{-# OPTIONS --type-in-type #-}

module Sigma where

open import Lib
open import CwF

Sg : ∀ {Γ}(A : Ty Γ) → Ty (Γ ▶ A) → Ty Γ
Sg A B = ty (λ γ → Σ (P A γ) λ α → P B (γ , α))
            (λ {(α , β) → R A α ⊎ R B β})

Sg[] : ∀ {Γ Δ A B}{σ : Sub Γ Δ} → Sg {Δ} A B [ σ ]T ≡ Sg (A [ σ ]T) (B [ σ ^ A ]T)
Sg[] = refl

Proj1 : ∀ {Γ A B} → Tm Γ (Sg A B) → Tm Γ A
Proj1 t = tm (λ γ → ₁ (P t γ)) (λ α* → R t (inj₁ α*))

Proj2 : ∀ {Γ A B}(t : Tm Γ (Sg A B)) → Tm Γ (B [ < Proj1 t > ]T)
Proj2 t = tm (λ γ → ₂ (P t γ)) (λ β* → R t (inj₂ β*))

Proj1[] : ∀ {Γ Δ A B t}{σ : Sub Γ Δ} → (Proj1 {Δ}{A}{B} t) [ σ ]t ≡ Proj1 (t [ σ ]t)
Proj1[] = refl

Proj2[] : ∀ {Γ Δ A B t}{σ : Sub Γ Δ} → (Proj2 {Δ}{A}{B} t) [ σ ]t ≡ Proj2 (t [ σ ]t)
Proj2[] = refl

Pair : ∀ {Γ A B}(t : Tm Γ A) → Tm Γ (B [ < t > ]T) → Tm Γ (Sg A B)
Pair t u = tm (λ γ → P t γ , P u γ) (⊎-elim _ (R t) (R u))

-- Pair[] is derivable in any model

Proj1β : ∀ {Γ A B t u} → Proj1 (Pair {Γ}{A}{B} t u) ≡ t
Proj1β = refl

Proj2β : ∀ {Γ A B t u} → Proj2 (Pair {Γ}{A}{B} t u) ≡ u
Proj2β = refl
