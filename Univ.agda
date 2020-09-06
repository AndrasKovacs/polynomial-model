
{-# OPTIONS --type-in-type #-}

module Univ where

open import Lib
open import CwF

U : ∀ {Γ} → Ty Γ
U {Γ} = ty (λ _ → Σ Set λ A → A → Set) (λ _ → ⊥)

El : ∀ {Γ} → Tm Γ U → Ty Γ
El {Γ} A = ty (λ γ → ₁ (P A γ)) (λ {γ} α → ₂ (P A γ) α)

El[] : ∀ {Γ Δ}{σ : Sub Γ Δ}{a} → (El {Δ} a) [ σ ]T ≡ El (a [ σ ]t)
El[] = refl

c : ∀ {Γ} → Ty Γ → Tm Γ U
c {Γ} A = tm (λ γ → (P A γ) , R A) ⊥-elim

cEl : ∀ {Γ a} → c (El {Γ} a) ≡ a
cEl {Γ} {a} = Tm≡ (λ _ → refl) (λ _ ())

Elc : ∀ {Γ A} → El {Γ} (c A) ≡ A
Elc {Γ} {A} = refl
