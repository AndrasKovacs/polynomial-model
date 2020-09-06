{-# OPTIONS --type-in-type #-}

module CwF where

open import Lib

record Con : Set₁ where
  constructor con
  field
    P : Set
    R : P → Set
open Con public

record Sub (Γ Δ : Con) : Set where
  constructor sub
  field
    P : P Γ → P Δ
    R : ∀ {γ} → R Δ (P γ) → R Γ γ
open Sub public

record Ty (Γ : Con) : Set₁ where
  constructor ty
  field
    P : Con.P Γ → Set
    R : ∀ {γ : Con.P Γ}(α : P γ) → Set
open Ty public

record Tm (Γ : Con) (A : Ty Γ) : Set₁ where
  constructor tm
  field
    P : (γ : P Γ) → P A γ
    R : ∀ {γ} → R A {γ} (P γ) → R Γ γ
open Tm public

abstract
  Sub≡ : ∀ {Γ Δ}{σ₀ σ₁ : Sub Γ Δ}
           (q₀₁ : ∀ γ → P σ₀ γ ≡ P σ₁ γ)
         → (∀ γ α → R σ₀ {γ} α ≡ R σ₁ (tr (R Δ) (q₀₁ γ) α))
         → σ₀ ≡ σ₁
  Sub≡ {Γ} {Δ} {sub q₀ r₀} {sub q₁ r₁} q₀₁ r₀₁ with ext q₀₁
  ... | refl = ap (sub q₀) (exti (λ {γ} → ext λ α →
                  r₀₁ _ α ◾ ap r₁ (tr (λ p → tr (R Δ) p α ≡ α) (UIP _ _) refl)))

  Ty≡ : ∀ {Γ}{A₀ A₁ : Ty Γ}(q₀₁ : ∀ γ → P A₀ γ ≡ P A₁ γ)
        → (∀ γ α → R A₀ {γ} α ≡ R A₁ (coe (q₀₁ γ) α)) → A₀ ≡ A₁
  Ty≡ {Γ} {ty q₀ r₀} {ty q₁ r₁} q₀₁ r₀₁ with ext q₀₁
  ... | refl = ap (ty q₀) (exti λ {γ} → ext λ α →
                 r₀₁ γ α ◾ ap r₁ (tr (λ p → coe p α ≡ α) (UIP _ _) refl))

  Tm≡ : ∀ {Γ A}{t₀ t₁ : Tm Γ A}
           (q₀₁ : ∀ γ → P t₀ γ ≡ P t₁ γ)
         → (∀ γ α → R t₀ {γ} α ≡ R t₁ (tr (R A) (q₀₁ γ) α))
         → t₀ ≡ t₁
  Tm≡ {Γ}{A}{tm q₀ r₀} {tm q₁ r₁} q₀₁ r₀₁ with ext q₀₁
  ... | refl = ap (tm q₀) (exti λ {γ} → ext λ α →
                 r₀₁ γ α ◾ ap r₁ (tr (λ p → tr (R A) p α ≡ α) (UIP _ _) refl))

∙ : Con
∙ = con ⊤ (λ _ → ⊥)

ε : ∀ {Γ} → Sub Γ ∙
ε = sub _ ⊥-elim

εη : ∀ {Γ}{σ : Sub Γ ∙} → σ ≡ ε
εη {Γ} {σ} = Sub≡ (λ _ → refl) (λ γ ∙* → ⊥-elim ∙*)

id : ∀ {Γ} → Sub Γ Γ
id {Γ} = sub (λ γ → γ) (λ γ* → γ*)

infixr 5 _∘_
_∘_ : ∀ {Γ Δ Σ} → Sub Δ Σ → Sub Γ Δ → Sub Γ Σ
sub q₀ r₀ ∘ sub q₁ r₁ = sub (λ γ → q₀ (q₁ γ)) (λ σ* → r₁ (r₀ σ*))

idl : ∀ {Γ Δ}{σ : Sub Γ Δ} → id ∘ σ ≡ σ
idl = refl

idr : ∀ {Γ Δ}{σ : Sub Γ Δ} → σ ∘ id ≡ σ
idr = refl

ass : ∀ {Γ Δ Σ Ξ}{σ : Sub Σ Ξ}{δ : Sub Δ Σ}{ν : Sub Γ Δ} → (σ ∘ δ) ∘ ν ≡ σ ∘ δ ∘ ν
ass = refl

infix 6 _[_]T
_[_]T : ∀ {Γ Δ} → Ty Δ → Sub Γ Δ → Ty Γ
_[_]T {Γ} {Δ} A σ = ty (λ γ → P A (P σ γ)) (R A)

[id]T : ∀ {Γ}{A : Ty Γ} → A [ id ]T ≡ A
[id]T = refl

[∘]T : ∀ {Γ Δ Σ}{A : Ty Σ}{σ : Sub Δ Σ}{δ : Sub Γ Δ} → A [ σ ]T [ δ ]T ≡ A [ σ ∘ δ ]T
[∘]T = refl

infix 6 _[_]t
_[_]t : ∀ {Γ Δ A}(t : Tm Δ A)(σ : Sub Γ Δ) → Tm Γ (A [ σ ]T)
_[_]t t σ = tm (λ γ → P t (P σ γ)) (λ α* → R σ (R t α*))


infixl 3 _▶_
_▶_ : (Γ : Con) → Ty Γ → Con
Γ ▶ A = con (Σ (P Γ) (P A)) (λ {(γ* , α*) → R Γ γ* ⊎ R A α*})

π₁ : ∀ {Γ Δ A} → Sub Γ (Δ ▶ A) → Sub Γ Δ
π₁ σ = sub (λ γ → ₁ (P σ γ)) (λ δ* → R σ (inj₁ δ*))

π₂ : ∀ {Γ Δ A}(σ : Sub Γ (Δ ▶ A)) → Tm Γ (A [ π₁ σ ]T)
π₂ σ = tm (λ γ → ₂ (P σ γ)) (λ α* → R σ (inj₂ α*))

infixl 3 _,ₛ_
_,ₛ_ : ∀ {Γ Δ A}(σ : Sub Γ Δ) → Tm Γ (A [ σ ]T) → Sub Γ (Δ ▶ A)
_,ₛ_ σ t = sub (λ γ → (P σ γ) , (P t γ)) (case (R σ) (R t))

π₁β : ∀ {Γ Δ A}{σ : Sub Γ Δ}{t : Tm Γ (A [ σ ]T)} → π₁ {A = A}(σ ,ₛ t) ≡ σ
π₁β {Γ} {Δ} {A} {σ} {t} = refl

π₂β : ∀ {Γ Δ A}{σ : Sub Γ Δ}{t : Tm Γ (A [ σ ]T)} → π₂ {A = A}(σ ,ₛ t) ≡ t
π₂β {Γ} {Δ} {A} {σ} {t} = refl

,ₛη : ∀ {Γ Δ A}{σ : Sub Γ (Δ ▶ A)} → (π₁ σ ,ₛ π₂ σ) ≡ σ
,ₛη {Γ} {Δ} {A} {σ} =
  Sub≡ (λ _ → refl)
       (λ γ → ⊎-elim (λ α →   case (λ δ* → R σ (inj₁ δ*)) (λ α* → R σ (inj₂ α*)) α
                            ≡ R σ α)
                    (λ _ → refl)
                    (λ _ → refl))

π₁∘ : ∀ {Γ Δ Σ A}{σ : Sub Δ (Σ ▶ A)}{δ : Sub Γ Δ} → π₁ σ ∘ δ ≡ π₁ (σ ∘ δ)
π₁∘ = refl

π₂∘ : ∀ {Γ Δ Σ A}{σ : Sub Δ (Σ ▶ A)}{δ : Sub Γ Δ} → π₂ σ [ δ ]t ≡ π₂ (σ ∘ δ)
π₂∘ = refl


-- abbreviations
------------------------------------------------------------

wk : ∀ {Γ A} → Sub (Γ ▶ A) Γ
wk = π₁ id

wk² : ∀ {Γ A B} → Sub (Γ ▶ A ▶ B) Γ
wk² = π₁ (π₁ id)

v₀ : ∀ {Γ A} → Tm (Γ ▶ A) (A [ wk ]T)
v₀ = π₂ id

v₁ : ∀ {Γ A B} → Tm (Γ ▶ A ▶ B) (A [ wk ∘ wk ]T)
v₁ = π₂ (π₁ id)

infixl 3 _^_
_^_ : ∀ {Γ Δ}(σ : Sub Γ Δ)(A : Ty Δ) → Sub (Γ ▶ A [ σ ]T) (Δ ▶ A)
_^_ σ A = σ ∘ wk ,ₛ v₀

<_> : ∀ {Γ A} → Tm Γ A → Sub Γ (Γ ▶ A)
< t > = id ,ₛ t
