
{-# OPTIONS --type-in-type --postfix-projections #-}

module Games.CoBiCCC where
open import Lib

-- Category of games following Abramsky/McCusker, where the first map goes
-- backwards.

-- This intuitively means that the opponent makes the first move, and the player
-- reacts. Since the model is from the "perspective" of the player (i.e. a player
-- can play (Γ * Δ) iff they can play Γ and Δ), the very first level lives in Setᵒᵖ.

-- This blocks dependent types, because it's not possible to take the opposite
-- of a CwF (because of dependent morphisms), only the opposite of a
-- simply-typed democratic CwF.

--------------------------------------------------------------------------------

record Con : Set where
  coinductive
  constructor send
  field
    M    : Set
    next : M → Con
open Con

record Sub (Γ Δ : Con) : Set where
  coinductive
  constructor sub
  field
    M    : M Δ → M Γ
    next : ∀ δ → Sub (next Δ δ) (next Γ (M δ))
open Sub

id : ∀ {Γ} → Sub Γ Γ
id {Γ} .M    γ = γ
id {Γ} .next γ = id {Γ .next γ}

infixr 5 _∘_
_∘_ : ∀ {Γ Δ Ξ} → Sub Δ Ξ → Sub Γ Δ → Sub Γ Ξ
(σ ∘ δ) .M    m = δ .M (σ .M m)
(σ ∘ δ) .next m = δ .next (σ .M m) ∘ σ .next m

infixl 4 _*_
_*_ : Con → Con → Con
(Γ * Δ) .M    = Γ .M ⊎ Δ .M
(Γ * Δ) .next = case (Γ .next) (Δ .next)

Proj₁ : ∀ {Γ Δ} → Sub (Γ * Δ) Γ
Proj₁ .M    γ = inj₁ γ
Proj₁ .next γ = id

Proj₂ : ∀ {Γ Δ} → Sub (Γ * Δ) Δ
Proj₂ .M    γ = inj₂ γ
Proj₂ .next γ = id

Pair : ∀ {Γ Δ Ξ} → Sub Γ Δ → Sub Γ Ξ → Sub Γ (Δ * Ξ)
Pair σ δ .M    = case (σ .M) (δ .M)
Pair σ δ .next = ⊎-elim _ (σ .next) (δ .next)

∙ : Con
∙ = send ⊥ λ ()

ε : ∀ {Γ} → Sub Γ ∙
ε = sub (λ ()) (λ ())

Bot : Con
Bot = send ⊤ λ _ → ∙

BotElim : ∀ {Γ} → Sub Bot Γ
BotElim = sub _ (λ γ → ε)

infixl 4 _+_
_+_ : Con → Con → Con
(Γ + Δ) .M            = Γ .M × Δ .M
(Γ + Δ) .next (γ , δ) = Γ .next γ * Δ .next δ

Inj₁ : ∀ {Γ Δ} → Sub Γ (Γ + Δ)
Inj₁ .M    (γ , δ) = γ
Inj₁ .next (γ , δ) = Proj₁

Inj₂ : ∀ {Γ Δ} → Sub Δ (Γ + Δ)
Inj₂ .M    (γ , δ) = δ
Inj₂ .next (γ , δ) = Proj₂

Copair : ∀ {Γ Δ Ξ} → Sub Γ Ξ → Sub Δ Ξ → Sub (Γ + Δ) Ξ
Copair σ δ .M    ξ = (σ .M ξ) , (δ .M ξ)
Copair σ δ .next ξ = Pair (σ .next ξ) (δ .next ξ)

Fun : Con → Con → Con
Fun Γ Δ .M                  = Δ .M × Bool
Fun Γ Δ .next (δ , b) .M    = {!!}
Fun Γ Δ .next (δ , b) .next = {!!}
