
module Identity where

open import Lib
open import CwF

Id : ∀ {i j Γ A} → Tm {i} Γ {j} A → Tm Γ A → Ty Γ j
Id t u = ty (λ γ → P t γ ≡ P u γ) (λ _ → ⊥)

Id[] : ∀ {i j k Γ Δ}{A : Ty Δ k}{t u : Tm Δ A}{σ : Sub {i} Γ {j} Δ}
       → Id t u [ σ ]T ≡ Id (t [ σ ]t) (u [ σ ]t)
Id[] = refl

Refl : ∀ {i j Γ A}(t : Tm {i} Γ {j} A) → Tm Γ (Id t t)
Refl t = tm (λ _ → refl) ⊥-elim

Refl[] : ∀ {i j k Γ Δ}{A : Ty Δ k}{t : Tm Δ A}{σ : Sub {i} Γ {j} Δ}
         → Refl t [ σ ]t ≡ Refl (t [ σ ]t)
Refl[] = Tm≡ (λ _ → refl) (λ γ → λ ())

UIP' : ∀ {i j Γ A}{t u : Tm {i} Γ {j} A}{e e' : Tm Γ (Id t u)} → Tm Γ (Id e e')
UIP' = tm (λ _ → UIP _ _) ⊥-elim

Tr : ∀ {i j k Γ A}(B : Ty (Γ ▶ A) k){t u : Tm {i} Γ {j} A}(e : Tm Γ (Id t u))
     → Tm Γ (B [ < t > ]T) → Tm Γ (B [ < u > ]T)
Tr {i}{j}{k}{Γ} {A} B e pt  =
  tm (λ γ → tr (λ x → P B (γ , x)) (P e γ) (P pt γ))
     (λ {γ} P* →
       R pt {γ} (J⁻¹ (λ _ e → R B (tr (λ x → P B (γ , x)) e (P pt γ))) (P e γ)
                     P*))

Tr[] : ∀ {i j k l Γ Δ A B t u e pt}{σ : Sub {i} Γ {j} Δ}
       → Tr {j}{k}{l} {Δ}{A} B {t} {u} e pt [ σ ]t
       ≡ Tr (B [ σ ^ A ]T) {t [ σ ]t}{u [ σ ]t} (e [ σ ]t) (pt [ σ ]t)
Tr[] = refl


Trβ : ∀ {i j k Γ A B t pt} → Tr {i}{j}{k}{Γ}{A} B {t}{t} (Refl t) pt ≡ pt
Trβ = refl

-- From this, the rules of plain intensional identity are derivable (in any model)
-- since J is derivable from Tr and UIP, and we also get J[] and Jβ.
