
module CwF where

open import Lib

record Con i : Set (lsuc i) where
  constructor con
  field
    P : Set i
    R : P → Set i
open Con public

record Sub {i}(Γ : Con i) {j} (Δ : Con j) : Set (i ⊔ j) where
  constructor sub
  field
    P : P Γ → P Δ
    R : ∀ {γ} → R Δ (P γ) → R Γ γ
open Sub public

record Ty {i}(Γ : Con i) j : Set (i ⊔ lsuc j) where
  constructor ty
  field
    P : Con.P Γ → Set j
    R : ∀ {γ : Con.P Γ}(α : P γ) → Set j
open Ty public

record Tm {i}(Γ : Con i){j} (A : Ty Γ j) : Set (i ⊔ j) where
  constructor tm
  field
    P : (γ : P Γ) → P A γ
    R : ∀ {γ} → R A {γ} (P γ) → R Γ γ
open Tm public

abstract
  Sub≡ : ∀ {i j Γ Δ}{σ₀ σ₁ : Sub {i} Γ {j} Δ}
           (q₀₁ : ∀ γ → P σ₀ γ ≡ P σ₁ γ)
         → (∀ γ α → R σ₀ {γ} α ≡ R σ₁ (tr (R Δ) (q₀₁ γ) α))
         → σ₀ ≡ σ₁
  Sub≡ {i}{j} {Γ} {Δ} {sub q₀ r₀} {sub q₁ r₁} q₀₁ r₀₁ with ext q₀₁
  ... | refl = ap (sub q₀) (exti (λ {γ} → ext λ α →
                  r₀₁ _ α ◾ ap r₁ (tr (λ p → tr (R Δ) p α ≡ α) (UIP _ _) refl)))

  Ty≡ : ∀ {i j}{Γ}{A₀ A₁ : Ty {i} Γ j}(q₀₁ : ∀ γ → P A₀ γ ≡ P A₁ γ)
        → (∀ γ α → R A₀ {γ} α ≡ R A₁ (coe (q₀₁ γ) α)) → A₀ ≡ A₁
  Ty≡ {i}{j} {Γ} {ty q₀ r₀} {ty q₁ r₁} q₀₁ r₀₁ with ext q₀₁
  ... | refl = ap (ty q₀) (exti λ {γ} → ext λ α →
                 r₀₁ γ α ◾ ap r₁ (tr (λ p → coe p α ≡ α) (UIP _ _) refl))

  Tm≡ : ∀ {i j }{Γ A}{t₀ t₁ : Tm {i} Γ {j} A}
           (q₀₁ : ∀ γ → P t₀ γ ≡ P t₁ γ)
         → (∀ γ α → R t₀ {γ} α ≡ R t₁ (tr (R A) (q₀₁ γ) α))
         → t₀ ≡ t₁
  Tm≡ {i}{j} {Γ}{A}{tm q₀ r₀} {tm q₁ r₁} q₀₁ r₀₁ with ext q₀₁
  ... | refl = ap (tm q₀) (exti λ {γ} → ext λ α →
                 r₀₁ γ α ◾ ap r₁ (tr (λ p → tr (R A) p α ≡ α) (UIP _ _) refl))

∙ : Con lzero
∙ = con ⊤ (λ _ → ⊥)

ε : ∀ {i}{Γ : Con i} → Sub Γ ∙
ε = sub _ ⊥-elim

εη : ∀ {i Γ}{σ : Sub {i} Γ ∙} → σ ≡ ε
εη = Sub≡ (λ _ → refl) (λ γ ∙* → ⊥-elim ∙*)

id : ∀ {i Γ} → Sub {i} Γ Γ
id = sub (λ γ → γ) (λ γ* → γ*)

infixr 5 _∘_
_∘_ : ∀ {i j k Γ Δ Σ} → Sub Δ Σ → Sub Γ {j} Δ → Sub {i} Γ {k} Σ
sub q₀ r₀ ∘ sub q₁ r₁ = sub (λ γ → q₀ (q₁ γ)) (λ σ* → r₁ (r₀ σ*))

idl : ∀ {i j Γ Δ}{σ : Sub {i} Γ {j} Δ} → id ∘ σ ≡ σ
idl = refl

idr : ∀ {i j Γ Δ}{σ : Sub {i} Γ {j} Δ} → σ ∘ id ≡ σ
idr = refl

ass : ∀ {i j k l Γ Δ Σ Ξ}{σ : Sub {k} Σ {l} Ξ}{δ : Sub Δ Σ}{ν : Sub {i} Γ {j} Δ}
      → (σ ∘ δ) ∘ ν ≡ σ ∘ δ ∘ ν
ass = refl

infix 6 _[_]T
_[_]T : ∀ {i j k Γ Δ} → Ty Δ k → Sub {i} Γ {j} Δ → Ty Γ k
_[_]T {i}{j}{k}{Γ} {Δ} A σ = ty (λ γ → P A (P σ γ)) (R A)

[id]T : ∀ {i j Γ}{A : Ty {i} Γ j} → A [ id ]T ≡ A
[id]T = refl

[∘]T : ∀ {i j k l Γ Δ Σ}{A : Ty {k} Σ l}{σ : Sub Δ Σ}{δ : Sub {i} Γ {j} Δ}
       → A [ σ ]T [ δ ]T ≡ A [ σ ∘ δ ]T
[∘]T = refl

infix 6 _[_]t
_[_]t : ∀ {i j k Γ Δ A}(t : Tm Δ {k} A)(σ : Sub {i} Γ {j} Δ) → Tm Γ (A [ σ ]T)
_[_]t t σ = tm (λ γ → P t (P σ γ)) (λ α* → R σ (R t α*))

infixl 3 _▶_
_▶_ : ∀ {i j}(Γ : Con i) → Ty Γ j → Con (i ⊔ j)
Γ ▶ A = con (Σ (P Γ) (P A)) (λ {(γ* , α*) → R Γ γ* ⊎ R A α*})

π₁ : ∀ {i j k Γ Δ}{A : Ty Δ k} → Sub Γ (Δ ▶ A) → Sub {i} Γ {j} Δ
π₁ σ = sub (λ γ → ₁ (P σ γ)) (λ δ* → R σ (inj₁ δ*))

π₂ : ∀ {i j k Γ Δ}{A : Ty {j} Δ k}(σ : Sub Γ (Δ ▶ A)) → Tm {i} Γ (A [ π₁ σ ]T)
π₂ σ = tm (λ γ → ₂ (P σ γ)) (λ α* → R σ (inj₂ α*))

infixl 3 _,ₛ_
_,ₛ_ : ∀ {i j k Γ Δ}{A : Ty Δ k}(σ : Sub {i} Γ {j} Δ) → Tm Γ (A [ σ ]T) → Sub Γ (Δ ▶ A)
_,ₛ_ σ t = sub (λ γ → (P σ γ) , (P t γ)) (case (R σ) (R t))

π₁β : ∀ {i j k Γ Δ}{A : Ty Δ k}{σ : Sub {i} Γ {j} Δ}{t : Tm Γ (A [ σ ]T)} → π₁ {A = A}(σ ,ₛ t) ≡ σ
π₁β = refl

π₂β : ∀ {i j k Γ Δ}{A : Ty Δ k}{σ : Sub {i} Γ {j} Δ}{t : Tm Γ (A [ σ ]T)} → π₂ {A = A}(σ ,ₛ t) ≡ t
π₂β = refl

,ₛη : ∀ {i j k Γ}{Δ : Con j}{A : Ty Δ k}{σ : Sub {i} Γ (Δ ▶ A)} → (π₁ σ ,ₛ π₂ σ) ≡ σ
,ₛη {i}{j}{k}{Γ} {Δ} {A} {σ} =
  Sub≡ (λ _ → refl)
       (λ γ → ⊎-elim (λ α →   case (λ δ* → R σ (inj₁ δ*)) (λ α* → R σ (inj₂ α*)) α
                            ≡ R σ α)
                    (λ _ → refl)
                    (λ _ → refl))

π₁∘ : ∀ {i j k l Γ Δ}{Σ : Con k}{A : Ty Σ l}{σ : Sub Δ (Σ ▶ A)}{δ : Sub {i} Γ {j} Δ}
      → π₁ σ ∘ δ ≡ π₁ (σ ∘ δ)
π₁∘ = refl

π₂∘ : ∀ {i j k l Γ Δ}{Σ : Con k}{A : Ty Σ l}{σ : Sub Δ (Σ ▶ A)}{δ : Sub {i} Γ {j} Δ}
      → π₂ σ [ δ ]t ≡ π₂ (σ ∘ δ)
π₂∘ = refl


-- abbreviations
------------------------------------------------------------

wk : ∀ {i j}{Γ : Con i}{A : Ty Γ j} → Sub (Γ ▶ A) Γ
wk = π₁ id

wk² : ∀ {i j k}{Γ : Con i}{A : Ty Γ j}{B : Ty (Γ ▶ A) k} → Sub (Γ ▶ A ▶ B) Γ
wk² = π₁ (π₁ id)

v₀ : ∀ {i j}{Γ : Con i}{A : Ty Γ j} → Tm (Γ ▶ A) (A [ wk ]T)
v₀ = π₂ id

v₁ : ∀ {i j k}{Γ : Con i}{A : Ty Γ j}{B : Ty (Γ ▶ A) k} → Tm (Γ ▶ A ▶ B) (A [ wk ∘ wk ]T)
v₁ = π₂ (π₁ id)

v₂ : ∀ {i j k l}{Γ : Con i}{A : Ty Γ j}{B : Ty (Γ ▶ A) k}
                {C : Ty (Γ ▶ A ▶ B) l}
     → Tm (Γ ▶ A ▶ B ▶ C) (A [ wk ∘ wk ∘ wk ]T)
v₂ = π₂ (π₁ (π₁ id))

infixl 3 _^_
_^_ : ∀ {i j k Γ Δ}(σ : Sub {i}Γ {j} Δ)(A : Ty Δ k) → Sub (Γ ▶ A [ σ ]T) (Δ ▶ A)
_^_ σ A = σ ∘ wk ,ₛ v₀

<_> : ∀ {i j Γ A} → Tm {i} Γ {j} A → Sub Γ (Γ ▶ A)
< t > = id ,ₛ t
