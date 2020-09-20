
{-# OPTIONS --type-in-type --postfix-projections #-}

module Games.CoBiCCC where
open import Lib

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

--------------------------------------------------------------------------------

-- tensor product
infixr 4 _⊗_
_⊗_ : Con → Con → Con
(Γ ⊗ Δ) .M                      = Γ .M ⊎ Δ .M
(Γ ⊗ Δ) .next (inj₁ γ) .M       = Γ .next γ .M
(Γ ⊗ Δ) .next (inj₁ γ) .next γ' = Γ .next γ .next γ' ⊗ Δ
(Γ ⊗ Δ) .next (inj₂ δ) .M       = Δ .next δ .M
(Γ ⊗ Δ) .next (inj₂ δ) .next δ' = Γ ⊗ Δ .next δ .next δ'

-- tensor product of a ℕ-indexed family
⊗ᵢ : (ℕ → Con) → Con
⊗ᵢ Γ .M                     = ∃ λ i → Γ i .M
⊗ᵢ Γ .next (i , γ) .M       = Γ i .next γ .M
⊗ᵢ Γ .next (i , γ) .next γ' = ⊗ᵢ λ j → decCase (λ {refl → Γ i .next γ .next γ'}) (λ _ → Γ j) (ℕ≟ i j)

-- Γ ! = Γ ⊗ Γ ⊗ Γ ...
infix 7 _!
_! : Con → Con
Γ ! = ⊗ᵢ (λ _ → Γ)

-- der : (Γ : ℕ → Con) → Sub (⊗ᵢ Γ) (Γ 0)
-- der Γ .M γ = 0 , γ
-- der Γ .next γ .M γ' = γ'
-- der Γ .next γ .next γ' = coe {!!} (der (λ j →
--           decCase (λ { refl → Γ 0 .next γ .next γ' }) (λ _ → Γ j) (ℕ≟ 0 j)))


-- infixr 3 _⊸_
-- _⊸_ : Con → Con → Con
-- (Γ ⊸ Δ) .M                      = Δ .M
-- (Γ ⊸ Δ) .next δ .M              = Γ .M ⊎ Δ .next δ .M
-- (Γ ⊸ Δ) .next δ .next (inj₁ γ)  = {!!}
-- (Γ ⊸ Δ) .next δ .next (inj₂ δ') = Γ ⊸ Δ .next δ .next δ'

-- -- ????? should work, since it's in the literature
-- Fun : Con → Con → Con
-- Fun Γ Δ .M                  = Δ .M × Bool
-- Fun Γ Δ .next (δ , b) .M    = {!!}
-- Fun Γ Δ .next (δ , b) .next = {!!}
