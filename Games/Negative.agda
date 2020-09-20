
{-# OPTIONS --type-in-type --postfix-projections #-}

module Games.Negative where
open import Lib

record Con : Set where
  inductive
  constructor con
  field
    M    : Set
    next : M → Con
open Con

record Sub (Γ Δ : Con) : Set where
  inductive
  constructor sub
  field
    next : ∀ (δ : M Δ) → (∃ λ δ' → Sub Γ (Δ .next δ .next δ'))  -- play
                       ⊎ (∃ λ γ  → Sub (Δ .next δ) (Γ .next γ)) -- switch
open Sub

id : ∀ {Γ} → Sub Γ Γ
id {con M next} = sub (λ δ → inj₂ (δ , id))

infixr 5 _∘_
_∘_  : ∀ {Γ Δ Ξ} → Sub Δ Ξ → Sub Γ Δ → Sub Γ Ξ

chatter : ∀ {Γ Δ Ξ}(δ : Δ .M)(ξ : Ξ .M) → Sub (Ξ .next ξ) (Δ .next δ) → Sub Γ Δ
          → Σ (Ξ .next ξ .M) (λ δ' → Sub Γ (Ξ .next ξ .next δ'))
          ⊎ Σ (Γ .M) (λ γ → Sub (Ξ .next ξ) (Γ .next γ))

(_∘_ {Γ}{Δ}{Ξ} (sub f) g) .next ξ with f ξ
... | inj₁ (ξ' , f') = inj₁ (ξ' , f' ∘ g)
... | inj₂ (δ , f')  = chatter {Ξ = Ξ} δ ξ f' g

chatter {Γ}{Δ}{Ξ} δ ξ f g with g .next δ
... | inj₂ (γ   , g') = inj₂ (γ , g' ∘ f)
... | inj₁ (δ'  , g') with f .next δ'
... | inj₂ (ξ'  , f') = inj₁ (ξ' , f' ∘ g')
... | inj₁ (δ'' , f') = chatter {Ξ = Ξ} δ'' ξ f' g'

Conᴼ Conᴾ : Con → Set
Conᴼ (con M next) = ∀ m   → Conᴾ (next m)
Conᴾ (con M next) = ∃ λ m → Conᴼ (next m)

Subᴾ : ∀ {Γ Δ} → Sub Γ Δ → Conᴾ Δ → Conᴾ Γ
Subᴼ : ∀ {Γ Δ} → Sub Γ Δ → Conᴼ Γ → Conᴼ Δ
Subᴼ {con M next} {con M' next'} (sub f) Δᴼ δ with f δ
... | inj₂ (γ  , f') = Subᴾ f' (Δᴼ γ)
... | inj₁ (δ' , f') with next' δ
... | con M'' next'' = δ' , Subᴼ f' Δᴼ
Subᴾ {con M next} {con M' next'} (sub f) (δ , Δᴼ) with f δ
... | inj₂ (γ , f')  = γ , Subᴼ f' Δᴼ
... | inj₁ (δ' , f') with next' δ
... | con M'' next'' = Subᴾ f' (Δᴼ δ')
