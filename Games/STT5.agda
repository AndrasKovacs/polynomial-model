
{-# OPTIONS --type-in-type --postfix-projections #-}

module Games.STT5 where

open import Lib

--------------------------------------------------------------------------------

record Con : Set where
  coinductive
  constructor send
  field
    Q    : Set
    step : Q → Con
open Con

record Sub (Γ Δ : Con) : Set where
  coinductive
  constructor sub
  field
    Q    : Q Γ → Q Δ
    step : ∀ q → Sub (step Δ (Q q)) (step Γ q)
open Sub

id : ∀ {Γ} → Sub Γ Γ
id .Q    q = q
id .step q = id

infixr 5 _∘_
_∘_ : ∀ {Γ Δ Ξ} → Sub Δ Ξ → Sub Γ Δ → Sub Γ Ξ
(σ ∘ δ) .Q    q = σ .Q (δ .Q q)
(σ ∘ δ) .step q = δ .step q ∘ σ .step (δ .Q q)

Bot : Con
Bot .Q    = ⊥
Bot .step ()

Init : ∀ {Γ} → Sub Bot Γ
Init .Q  ()
Init .step ()

Top : Con
Top .Q      = ⊤
Top .step _ = Bot

Final : ∀ {Γ} → Sub Γ Top
Final .Q    _ = _
Final .step _ = Init

--------------------------------------------------------------------------------

record Conᴬ (Γ : Con) : Set
record Conᴮ (Γ : Con) : Set

record Conᴬ Γ where
  coinductive
  field
    move : Γ .Q
    step : Conᴮ (Γ .step move)
open Conᴬ

record Conᴮ Γ where
  coinductive
  field
    step : ∀ q → Conᴬ (Γ .step q)
open Conᴮ

Subᴬ : ∀ {Γ Δ} → Sub Γ Δ → Conᴬ Γ → Conᴬ Δ
Subᴮ : ∀ {Γ Δ} → Sub Δ Γ → Conᴮ Γ → Conᴮ Δ
Subᴬ σ γ .move   = σ .Q (γ .move)
Subᴬ σ γ .step   = Subᴮ (σ .step (γ .move)) (γ .step)
Subᴮ σ γ .step q = Subᴬ (σ .step q) (γ .step (σ .Q q))

--------------------------------------------------------------------------------

infixr 4 _+_
_+_ : Con → Con → Con
(Γ + Δ) .Q    = Γ .Q ⊎ Δ .Q
(Γ + Δ) .step = case (Γ .step) (Δ .step)

Inj₁ : ∀ {Γ Δ} → Sub Γ (Γ + Δ)
Inj₁ .Q    q = inj₁ q
Inj₁ .step q = id

Inj₂ : ∀ {Γ Δ} → Sub Δ (Γ + Δ)
Inj₂ .Q    q = inj₂ q
Inj₂ .step q = id

Copair : ∀ {Γ Δ Ξ} → Sub Γ Ξ → Sub Δ Ξ → Sub (Γ + Δ) Ξ
Copair σ δ .Q    = case (σ .Q) (δ .Q)
Copair σ δ .step = ⊎-elim _ (σ .step) (δ .step)

--------------------------------------------------------------------------------

infixl 4 _*_
_*_ : Con → Con → Con
(Γ * Δ) .Q             = Γ .Q × Δ .Q
(Γ * Δ) .step (q , q') = Γ .step q + Δ .step q'

Proj₁ : ∀ {Γ Δ} → Sub (Γ * Δ) Γ
Proj₁ .Q    (q , q') = q
Proj₁ .step (q , q') = Inj₁

Proj₂ : ∀ {Γ Δ} → Sub (Γ * Δ) Δ
Proj₂ .Q    (q , q') = q'
Proj₂ .step (q , q') = Inj₂

Pair : ∀ {Γ Δ Ξ} → Sub Γ Δ → Sub Γ Ξ → Sub Γ (Δ * Ξ)
Pair σ δ .Q    q = (σ .Q q) , (δ .Q q)
Pair σ δ .step q = Copair (σ .step q) (δ .step q)


-- Exponential
--------------------------------------------------------------------------------

_⇒_ : Con → Con → Con
(Γ ⇒ Δ) .Q                         = Sub (send (Γ .Q) λ q → Top + Γ .step q) Δ
(Γ ⇒ Δ) .step σ .Q                 = ∃₂ λ q a' → isLeft (σ .step q .Q a')
(Γ ⇒ Δ) .step σ .step (q , a' , p) = Δ .step (σ .Q q) .step a'

Lam : ∀ {Γ B C} → Sub (Γ * B) C → Sub Γ (B ⇒ C)
Lam σ .Q q .Q    q'           = σ .Q (q , q')
Lam σ .Q q .step q' .Q    a'' = lmap (σ .step _ .Q a'') _
Lam σ .Q q .step q' .step a'' with σ .step _ .Q a'' | σ .step _ .step a''
... | inj₁ a  | σ' = Init
... | inj₂ a' | σ' = σ'
Lam σ .step q .Q (q' , a'' , p) with σ .step _ .Q a''
... | inj₁ a = a
... | inj₂ _ = ⊥-elim p
Lam σ .step q .step (q' , a'' , p) with σ .step _ .Q a'' | σ .step _ .step a''
... | inj₁ a | σ' = σ'
... | inj₂ _ | _  = ⊥-elim p

App : ∀ {Γ B C} → Sub Γ (B ⇒ C) → Sub (Γ * B) C
App σ .Q    (q , q') = σ .Q q .Q q'
App σ .step (q , q') .Q a'' with σ .Q q .step q' .Q a'' | inspect (σ .Q q .step q' .Q) a''
                               | σ .Q q .step q' .step a''
... | inj₁ tt | [ eq ] | σ' = inj₁ (σ .step q .Q (q' , a'' , tr isLeft (eq ⁻¹) tt))
... | inj₂ a' | [ eq ] | σ' = inj₂ a'
App σ .step (q , q') .step a'' with σ .Q q .step q' .Q a'' | inspect (σ .Q q .step q' .Q) a''
                                  | σ .Q q .step q' .step a''
... | inj₁ tt | [ eq ] | σ' = σ .step q .step (q' , a'' , tr isLeft (eq ⁻¹) tt)
... | inj₂ a' | eq     | σ' = σ'

-- Lam∘ : ∀ {Γ Δ B C}(σ : Sub Γ Δ)(δ : Sub (Δ * B) C)
--      → Lam δ ∘ σ ≡ Lam (δ ∘ Pair (σ ∘ Proj₁) Proj₂)

fromTotal : ∀ {Γ Δ} → Sub Γ Δ → Conᴬ (Γ ⇒ Δ)
fromTotal σ .move .Q    q = σ .Q q
fromTotal σ .move .step q = Inj₂ ∘ σ .step q
fromTotal σ .step .step ()

toTotal : ∀ {Γ Δ} → Sub Top (Γ ⇒ Δ) → Sub Γ Δ
toTotal σ = App σ ∘ Pair Final id


--------------------------------------------------------------------------------

Nat : Con
Nat .Q      = ℕ
Nat .step _ = Bot

Zero : Sub Top Nat
Zero .Q    _ = zero
Zero .step _ = Init

Suc : Sub Nat Nat
Suc .Q      = suc
Suc .step _ = Init

NatRec : ∀ {Γ} → Sub Top Γ → Sub Γ Γ → Sub Nat Γ
NatRec fz fs .Q    = natElim _ (fz .Q tt) (λ _ → fs .Q)
NatRec fz fs .step = natElim _ (fz .step tt) λ n σ → σ ∘ fs .step (NatRec fz fs .Q n)

NatRec' : ∀ {Γ} → Sub Top Γ → Sub Γ Γ → Sub Nat Γ
NatRec' fz fs .Q zero       = fz .Q tt
NatRec' fz fs .Q (suc n)    = fs .Q (NatRec' fz fs .Q n)
NatRec' fz fs .step zero    = fz .step tt
NatRec' fz fs .step (suc n) = NatRec' fz fs .step n ∘ fs .step (NatRec' fz fs .Q n)

--------------------------------------------------------------------------------

data list (A : Set) : Set where
  [] : list A
  _∷_ : A → list A → list A
infixr 4 _∷_

List : Con → Con
List Γ .Q             = list (Γ .Q)
List Γ .step []       = Bot
List Γ .step (q ∷ qs) = Γ .step q + List Γ .step qs
