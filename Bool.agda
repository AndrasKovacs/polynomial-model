
module Bool where

open import Lib hiding (Bool)
import Lib as L

open import CwF

Bool : ∀ {i Γ} → Ty {i} Γ lzero
Bool = ty (λ _ → L.Bool) λ _ → ⊥

Bool[] : ∀ {i j Γ Δ}{σ : Sub {i} Γ {j} Δ} → Bool [ σ ]T ≡ Bool
Bool[] = refl

True : ∀ {i Γ} → Tm {i} Γ Bool
True = tm (λ _ → true) λ ()

True[] : ∀ {i j Γ Δ}{σ : Sub {i} Γ {j} Δ} → True [ σ ]t ≡ True
True[] = Tm≡ (λ _ → refl) (λ _ ())

False : ∀ {i Γ} → Tm {i} Γ Bool
False = tm (λ _ → false) λ ()

False[] : ∀ {i j Γ Δ}{σ : Sub {i} Γ {j} Δ} → False [ σ ]t ≡ False
False[] = Tm≡ (λ _ → refl) (λ _ ())

BoolElim :
  ∀ {i j}
    {Γ : Con i}
    (Pr : Ty (Γ ▶ Bool) j)
    (PT : Tm Γ (Pr [ < True > ]T))
    (PF : Tm Γ (Pr [ < False > ]T))
    (b  : Tm Γ Bool)
  →  Tm Γ (Pr [ < b > ]T)
P (BoolElim {i}{j}{Γ} Pr PT PF b) γ =
  boolElim (λ b → P Pr (γ , b)) (P PT γ) (P PF γ) (P b γ)
R (BoolElim {i}{j}{Γ} Pr PT PF b) {γ} =
  boolElim (λ b → R Pr (boolElim (λ b → P Pr (γ , b)) (P PT γ) (P PF γ) b)
                → R Γ γ)
           (R PT) (R PF) (P b γ)

Trueβ : ∀ {i j Γ Pr PT PF} → BoolElim {i}{j}{Γ} Pr PT PF True ≡ PT
Trueβ = refl

Falseβ : ∀ {i j Γ Pr PT PF} → BoolElim {i}{j}{Γ} Pr PT PF False ≡ PF
Falseβ = refl

BoolElim[] :
  ∀ {i j k Γ Δ Pr PT PF b}{σ : Sub {i} Γ {k} Δ}
  → BoolElim {k}{j}{Δ} Pr PT PF b [ σ ]t
  ≡ BoolElim (Pr [ σ ^ Bool ]T) (PT [ σ ]t) (PF [ σ ]t) (b [ σ ]t)
BoolElim[] {i}{j}{k}{Γ} {Δ} {Pr} {PT} {PF} {b} {σ} = Tm≡ (λ _ → refl) R≡ where
  R≡ : _
  R≡ γ α with P b (P σ γ)
  ... | false = refl
  ... | true  = refl
