
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

record Sub≡ {Γ Δ}(σ δ : Sub Γ Δ) : Set where
  coinductive
  constructor sub≡
  field
    Q    : ∀ q → σ .Q q ≡ δ .Q q
    step : ∀ q → Sub≡ (tr (λ x → Sub (step Δ x) (step Γ q)) (Q q) (σ .step q))
                      (δ .step q)
open Sub≡

infix 6 _ˢ⁻¹
{-# TERMINATING #-}
_ˢ⁻¹ : ∀ {Γ Δ σ δ} → Sub≡ {Γ}{Δ} σ δ → Sub≡ δ σ
(e ˢ⁻¹) .Q    q = e .Q q ⁻¹
_ˢ⁻¹ {Γ} {Δ} {σ} {δ} e .step q =
   J (λ δQq eQq →
          (δstepq : Sub (step Δ (δQq)) (step Γ q))
        → (hyp : Sub≡ (δstepq)
                      (tr (λ x → Sub (step Δ x) (step Γ q)) (eQq) (σ .step q)))
        → Sub≡ (tr (λ x → Sub (step Δ x) (step Γ q)) (eQq ⁻¹) (δstepq))
               (σ .step q))
     (e .Q q)
     (λ _ hyp → hyp)
     (δ .step q)
     (e .step q ˢ⁻¹)

infixr 4 _ˢ◾_
postulate
  _ˢ◾_ : ∀ {Γ Δ σ δ ν} → Sub≡ {Γ}{Δ} σ δ → Sub≡ δ ν → Sub≡ σ ν


id : ∀ {Γ} → Sub Γ Γ
id .Q    q = q
id .step q = id

infixr 5 _∘_
_∘_ : ∀ {Γ Δ Ξ} → Sub Δ Ξ → Sub Γ Δ → Sub Γ Ξ
(σ ∘ δ) .Q    q = σ .Q (δ .Q q)
(σ ∘ δ) .step q = δ .step q ∘ σ .step (δ .Q q)

idl : ∀ {Γ Δ}(σ : Sub Γ Δ) → Sub≡ (id ∘ σ) σ
idr : ∀ {Γ Δ}(σ : Sub Γ Δ) → Sub≡ (σ ∘ id) σ
idl σ .Q    _ = refl
idl σ .step q = idr (σ .step q)
idr σ .Q    _ = refl
idr σ .step q = idl (σ .step q)

{-# TERMINATING #-}
ass : ∀ {Γ Δ Σ Ξ}(σ : Sub Σ Ξ)(δ : Sub Δ Σ)(ν : Sub Γ Δ)
      → Sub≡ ((σ ∘ δ) ∘ ν) (σ ∘ δ ∘ ν)
ass σ δ ν .Q    _ = refl
ass σ δ ν .step q = ass (ν .step q) (δ .step (ν .Q q)) (σ .step (δ .Q (ν .Q q))) ˢ⁻¹

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

Bracket : ∀ {Γ Γ' Δ Δ'} → Sub Γ Γ' → Sub Δ Δ' → Sub (Γ + Δ) (Γ' + Δ')
Bracket f g = Copair (Inj₁ ∘ f) (Inj₂ ∘ g)

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
NatRec z s .Q    zero    = z .Q tt
NatRec z s .Q    (suc n) = s .Q (NatRec z s .Q n)
NatRec z s .step zero    = z .step tt
NatRec z s .step (suc n) = NatRec z s .step n ∘ s .step (NatRec z s .Q n)

Add : Sub Nat (Nat ⇒ Nat)
Add = NatRec (Lam Proj₂) (Lam (Suc ∘ App Proj₁ ∘ Pair id Proj₂))

--------------------------------------------------------------------------------

data list (A : Set) : Set where
  [] : list A
  _∷_ : A → list A → list A
infixr 4 _∷_

List : Con → Con
List Γ .Q             = list (Γ .Q)
List Γ .step []       = Bot
List Γ .step (q ∷ qs) = Γ .step q + List Γ .step qs

Nil : ∀ {Γ} → Sub Top (List Γ)
Nil .Q    _ = []
Nil .step _ = Init

Cons : ∀ {Γ} → Sub (Γ * List Γ) (List Γ)
Cons .Q    (q , qs) = q ∷ qs
Cons .step (q , qs) = id

Foldr : ∀ {Γ Δ} → Sub Top Δ → Sub (Γ * Δ) Δ → Sub (List Γ) Δ
Foldr n c .Q    []       = n .Q tt
Foldr n c .Q    (q ∷ qs) = c .Q (q , Foldr n c .Q qs)
Foldr n c .step []       = n .step tt
Foldr n c .step (q ∷ qs) = Bracket id (Foldr n c .step qs) ∘ c .step (q , Foldr n c .Q qs)

--------------------------------------------------------------------------------

-- λ f. f 0 + f 1
ex1 : Sub (Nat ⇒ Nat) Nat
ex1 = App Add ∘ Pair (App id ∘ Pair id (Zero ∘ Final))
                     (App id ∘ Pair id (Suc ∘ Zero ∘ Final))

fromTotal : ∀ {Γ Δ} → Sub Γ Δ → Sub (send (Q Γ) λ q → Top + step Γ q) Δ
fromTotal σ .Q = σ .Q
fromTotal σ .step q .Q    q' = inj₂ (σ .step q .Q q')
fromTotal σ .step q .step q' = σ .step q .step q'

foo = ex1 .Q (fromTotal id)
