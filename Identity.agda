
{-# OPTIONS --type-in-type #-}

module Identity where

open import Lib
open import CwF

Id : ∀ {Γ A} → Tm Γ A → Tm Γ A → Ty Γ
Id {Γ}{A} t u = ty (λ γ → P t γ ≡ P u γ) (λ _ → ⊥)

Id[] : ∀ {Γ Δ A t u}{σ : Sub Γ Δ} → Id {Δ}{A} t u [ σ ]T ≡ Id (t [ σ ]t) (u [ σ ]t)
Id[] = refl

Refl : ∀ {Γ A}(t : Tm Γ A) → Tm Γ (Id t t)
Refl t = tm (λ _ → refl) ⊥-elim

Refl[] : ∀ {Γ Δ A t}{σ : Sub Γ Δ} → Refl {Δ}{A} t [ σ ]t ≡ Refl (t [ σ ]t)
Refl[] {Γ} {Δ} {A} {t} {σ} = Tm≡ (λ _ → refl) (λ γ → λ ())

UIP' : ∀ {Γ A}{t u : Tm Γ A}{e e' : Tm Γ (Id t u)} → Tm Γ (Id e e')
UIP' {Γ} {A} {t} {u} {e} {e'} = tm (λ _ → UIP _ _) ⊥-elim

Tr : ∀ {Γ A}(B : Ty (Γ ▶ A)){t u : Tm Γ A}(e : Tm Γ (Id t u))
     → Tm Γ (B [ < t > ]T) → Tm Γ (B [ < u > ]T)
Tr {Γ} {A} B e pt  =
  tm (λ γ → tr (λ x → P B (γ , x)) (P e γ) (P pt γ))
     (λ {γ} P* →
       R pt {γ} (J⁻¹ (λ _ e → R B (tr (λ x → P B (γ , x)) e (P pt γ))) (P e γ)
                     P*))

Tr[] : ∀ {Γ Δ A B t u e pt}{σ : Sub Γ Δ}
       → Tr {Δ}{A} B {t} {u} e pt [ σ ]t
       ≡ Tr (B [ σ ^ A ]T) {t [ σ ]t}{u [ σ ]t} (e [ σ ]t) (pt [ σ ]t)
Tr[] {Γ} {Δ} {A} {B} {t} {u} {e} {pt} {σ} =
  refl

Trβ : ∀ {Γ A B t pt} → Tr {Γ}{A} B {t}{t} (Refl t) pt ≡ pt
Trβ = refl

-- From this, the rules of plain intensional identity are derivable (in any model)
-- since J is derivable from Tr and UIP, and we also get J[] and Jβ.
