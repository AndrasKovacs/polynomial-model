{-# OPTIONS --type-in-type #-}

module Bool where

open import Lib hiding (Bool)
import Lib as L

open import CwF

Bool : ∀ {Γ} → Ty Γ
Bool = ty (λ _ → L.Bool) λ _ → ⊥

Bool[] : ∀ {Γ Δ}{σ : Sub Γ Δ} → Bool [ σ ]T ≡ Bool
Bool[] = refl

True : ∀ {Γ} → Tm Γ Bool
True = tm (λ _ → true) λ ()

True[] : ∀ {Γ Δ}{σ : Sub Γ Δ} → True [ σ ]t ≡ True
True[] = Tm≡ (λ _ → refl) (λ _ ())

False : ∀ {Γ} → Tm Γ Bool
False = tm (λ _ → false) λ ()

False[] : ∀ {Γ Δ}{σ : Sub Γ Δ} → False [ σ ]t ≡ False
False[] = Tm≡ (λ _ → refl) (λ _ ())

BoolElim :
  ∀ {Γ}(Pr : Ty (Γ ▶ Bool))
       (PT : Tm Γ (Pr [ < True > ]T))
       (PF : Tm Γ (Pr [ < False > ]T))
       (b  : Tm Γ Bool)
  →    Tm Γ (Pr [ < b > ]T)
P (BoolElim {Γ} Pr PT PF b) γ =
  boolElim (λ b → P Pr (γ , b)) (P PT γ) (P PF γ) (P b γ)
R (BoolElim {Γ} Pr PT PF b) {γ} =
  boolElim (λ b → R Pr (boolElim (λ b → P Pr (γ , b)) (P PT γ) (P PF γ) b)
                → R Γ γ)
           (R PT) (R PF) (P b γ)

Trueβ : ∀ {Γ Pr PT PF} → BoolElim {Γ} Pr PT PF True ≡ PT
Trueβ = refl

Falseβ : ∀ {Γ Pr PT PF} → BoolElim {Γ} Pr PT PF False ≡ PF
Falseβ = refl

BoolElim[] :
  ∀ {Γ Δ Pr PT PF b}{σ : Sub Γ Δ}
  → BoolElim {Δ} Pr PT PF b [ σ ]t
  ≡ BoolElim (Pr [ σ ^ Bool ]T) (PT [ σ ]t) (PF [ σ ]t) (b [ σ ]t)
BoolElim[] {Γ} {Δ} {Pr} {PT} {PF} {b} {σ} = Tm≡ (λ _ → refl) R≡ where
  R≡ : _
  R≡ γ α with P b (P σ γ)
  ... | false = refl
  ... | true  = refl
