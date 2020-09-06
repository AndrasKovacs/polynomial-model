
module Sigma where

open import Lib
open import CwF

Sg : ∀ {i j k Γ}(A : Ty {i} Γ j) → Ty (Γ ▶ A) k → Ty Γ (j ⊔ k)
Sg A B = ty (λ γ → Σ (P A γ) λ α → P B (γ , α))
            (λ {(α , β) → R A α ⊎ R B β})

Sg[] : ∀ {i j k l Γ Δ A B}{σ : Sub {i} Γ Δ}
       → Sg {j}{k}{l}{Δ} A B [ σ ]T ≡ Sg (A [ σ ]T) (B [ σ ^ A ]T)
Sg[] = refl

Proj1 : ∀ {i j k Γ A B} → Tm Γ (Sg {i}{j}{k} A B) → Tm Γ A
Proj1 t = tm (λ γ → ₁ (P t γ)) (λ α* → R t (inj₁ α*))

Proj2 : ∀ {i j k Γ A B}(t : Tm Γ (Sg {i}{j}{k} A B)) → Tm Γ (B [ < Proj1 t > ]T)
Proj2 t = tm (λ γ → ₂ (P t γ)) (λ β* → R t (inj₂ β*))

Proj1[] : ∀ {i j k l Γ Δ A B t}{σ : Sub {i} Γ Δ}
          → (Proj1 {j}{k}{l}{Δ}{A}{B} t) [ σ ]t ≡ Proj1 (t [ σ ]t)
Proj1[] = refl

Proj2[] : ∀ {i j k l Γ Δ A B t}{σ : Sub {i} Γ Δ}
          → (Proj2 {j}{k}{l}{Δ}{A}{B} t) [ σ ]t ≡ Proj2 (t [ σ ]t)
Proj2[] = refl

Pair : ∀ {i j k Γ A B}(t : Tm Γ A) → Tm Γ (B [ < t > ]T) → Tm Γ (Sg {i}{j}{k}A B)
Pair t u = tm (λ γ → P t γ , P u γ) (⊎-elim _ (R t) (R u))

-- Pair[] is derivable in any model

Proj1β : ∀ {i j k Γ A B t u} → Proj1 (Pair {i}{j}{k}{Γ}{A}{B} t u) ≡ t
Proj1β = refl

Proj2β : ∀ {i j k Γ A B t u} → Proj2 (Pair {i}{j}{k}{Γ}{A}{B} t u) ≡ u
Proj2β = refl
