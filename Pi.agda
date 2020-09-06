{-# OPTIONS --type-in-type #-}

module Pi where

open import Lib
open import CwF

Π : ∀ {Γ}(A : Ty Γ) → Ty (Γ ▶ A) → Ty Γ
P (Π {Γ} A B) γ     = (α : P A γ) → ∃ λ (fα : P B (γ , α)) → R B fα → ⊤ ⊎ R A α
R (Π {Γ} A B) {γ} f = ∃₂ λ (α : P A γ)(fα* : R B (₁ (f α))) → isLeft (₂ (f α) fα*)

Π[] : ∀ {Γ Δ}{σ : Sub Γ Δ}{A B} → Π {Δ} A B [ σ ]T ≡ Π (A [ σ ]T) (B [ σ ^ A ]T)
Π[] = refl

app : ∀ {Γ A B} → Tm Γ (Π A B) → Tm (Γ ▶ A) B
P (app {Γ} {A} {B} t) (γ , α)    = ₁ (P t γ α)
R (app {Γ} {A} {B} t) {γ , α} β* = lmap (₂ (P t γ α) β*) (λ p _ → R t (α , β* , p))

lam : ∀ {Γ A B} → Tm (Γ ▶ A) B → Tm Γ (Π A B)
P (lam {Γ} {A} {B} t) γ α          = (P t (γ , α)) , (λ β* → lmap (R t β*) _)
R (lam {Γ} {A} {B} t) (α , β* , p) = getLeft (R t β*) (lmap-isLeft← p)

app[] :
  ∀ {Γ Δ A B}{t : Tm Δ (Π A B)}{σ : Sub Γ Δ}
  → app (t [ σ ]t) ≡ app t [ σ ∘ π₁ id ,ₛ π₂ id ]t
app[] {Γ} {Δ} {A} {B} {t} {σ} =
  Tm≡ (λ {(γ , α) → refl})
      (λ {(γ , α) tα* →
         lmap-lmap (₂ (P t (P σ γ) α) tα*)
                   (λ p _ → R t (α , tα* , p))
                   (λ _ → R σ) ⁻¹
       ◾ case-lmap (R σ)
                   (lmap (₂ (P t (P σ γ) α) tα*)
                   (λ p _ → R t (α , tα* , p))) ⁻¹
       })

-- lam[] is derivable in any model

Πβ : ∀ {Γ A B t} → app (lam {Γ}{A}{B} t) ≡ t
Πβ {Γ} {A} {B} {t} =
  Tm≡ (λ _ → refl)
      (λ {(γ , α) β* →
         ⊎-elim (λ ab → lmap (lmap ab (λ _ _ → tt))
                          (λ p _ → getLeft ab (lmap-isLeft← p))
                        ≡ ab)
                (λ _ → refl) (λ _ → refl) (R t β*)
      })

Πη : ∀ {Γ A B t} → lam {Γ}{A}{B} (app t) ≡ t
Πη {Γ} {A} {B} {t} = Tm≡ P≡ R≡ where
  P≡ : (γ : P Γ) → P (lam (app t)) γ ≡ P t γ
  P≡ γ = ext λ α → ,≡ refl (ext λ β* → lmap-lmap (₂ (P t γ α) β*) _ _ ◾ lmap-⊤ _)

  R≡ : (γ : P Γ) (α : R (Π A B) (P (lam (app t)) γ))
       → R (lam (app t)) α ≡ R t (tr (R (Π A B)) (P≡ γ) α)
  R≡ γ (α , α* , p) =
      getLeft-lmap (₂ (P t γ α) α*) (λ p₁ _ → R t (α , α* , p₁)) (lmap-isLeft← p)
    ◾ ap (R t)
         ( ,≡ (tr-const (P≡ γ) α ⁻¹)
              (  tr-Σ (λ a → R B (₁ (P t γ a))) (λ {(a , fα*) → isLeft (₂ (P t γ a) fα*)})
                      (tr-const (P≡ γ) α ⁻¹) (α* , lmap-isLeft← (lmap-isLeft← p))
               ◾ ,≡ (tr-swap (λ a → R B (₁ (P t γ a))) (tr-const (P≡ γ) α ⁻¹) α*
                             (tr (λ { (f , a) → R B (₁ (f a)) }) (,≡ (P≡ γ) refl) α*)
                             (((coe-UIP _ α* ⁻¹
                              ◾ coe-∘
                                  (ap (λ { (f , a) → R B (₁ (f a)) }) (,≡ (P≡ γ) refl))
                                  (ap (λ a → R B (₁ (P t γ a))) ((tr-const (P≡ γ) α ⁻¹) ⁻¹)) α* ⁻¹)
                              ◾ ap (coe (ap (λ a → R B (₁ (P t γ a)))
                                        ((tr-const (P≡ γ) α ⁻¹) ⁻¹)))
                                 (tr-coe (λ { (f , a) → R B (₁ (f a)) })
                                        (,≡ (P≡ γ) refl) α*) ⁻¹)
                              ◾ tr-coe (λ a → R B (₁ (P t γ a)))
                                       ((tr-const (P≡ γ) α ⁻¹) ⁻¹) _ ⁻¹))
                    isLeft-prop
               ◾ tr-Σ (λ {(f , a) → R B (₁ (f a))})
                       (λ {((f , a) , fα*) → isLeft (₂ (f a) fα*)})
                       (,≡ (P≡ γ) refl)
                       (α* , p) ⁻¹ )
         ◾ tr-Σ (λ f → P A γ)
                (λ {(f , a) → Σ (R B (₁ (f a))) (λ fα* → isLeft (₂ (f a) fα*))})
                (P≡ γ) (α , α* , p) ⁻¹)
