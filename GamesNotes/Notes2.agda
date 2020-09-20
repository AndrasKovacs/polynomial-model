
{-# OPTIONS --type-in-type --rewriting --postfix-projections #-}

module Games.Notes2 where

open import Data.Unit
open import Data.Empty
open import Data.Product renaming (proj₁ to ₁; proj₂ to ₂)
open import Data.Bool
open import Relation.Binary.PropositionalEquality
  renaming (trans to infixr 4 _◾_; subst to tr; cong to ap; sym to infix 6 _⁻¹)
import Axiom.Extensionality.Propositional as Axiom
open import Function hiding (_∘_; id)
open import Data.Sum

case : ∀ {i j k}{A : Set i}{B : Set j}{C : Set k} → (A → C) → (B → C) → A ⊎ B → C
case f g (inj₁ a) = f a
case f g (inj₂ b) = g b

{-# BUILTIN REWRITE _≡_ #-}

coe : ∀ {i}{A B : Set i} → A ≡ B → A → B
coe refl x = x

postulate
  ext  : ∀ {i j} → Axiom.Extensionality i j
  exti : ∀ {i j} → Axiom.ExtensionalityImplicit i j

-- record Con' : Set where
--   inductive
--   constructor con'
--   field
--     A    : Set
--     B    : A → Set
--     step : ∀ a → B a → Con'
-- open Con'

data Con : Set where
  next : (A : Set)(B : A → ∃ λ B → B → Con) → Con

Sub : Con → Con → Set
Sub (next A f) (next A' f') =
  ∀ a → ∃ λ a' → ∀ b' → ∃ λ b → Sub (f a .₂ b) (f' a' .₂ b')

infixr 5 _∘_
_∘_ : ∀ {Γ Δ Ξ} → Sub Δ Ξ → Sub Γ Δ → Sub Γ Ξ
_∘_ {next A f} {next A' f'} {next A'' f''} σ δ =
    λ a   → (σ (δ a .₁) .₁)
  , λ b'' → δ a .₂ (σ (δ a .₁) .₂ b'' .₁) .₁
  , σ (δ a .₁) .₂ b'' .₂ ∘ δ a .₂ (σ (δ a .₁) .₂ b'' .₁) .₂

id : ∀ {Γ} → Sub Γ Γ
id {next A f} = λ a → a , λ b' → b' , id

∙ : Con
∙ = next ⊤ λ _ → ⊥ , λ ()

ε : ∀ {Γ} → Sub Γ ∙
ε {next A f} a = tt , (λ ())

Bot : Con
Bot = next ⊥ λ ()

Bot-Init : ∀ {Γ} → Sub Bot Γ
Bot-Init {next A f} ()

Ty : Con → Set
Ty (next A f) =
  ∀ a → ∃ λ Aᴰ → Aᴰ → ∃ λ Bᴰ → Bᴰ → ∃ λ b → Ty (f a .₂ b)

Tm : ∀ Γ → Ty Γ → Set
Tm (next A f) Aᴰ = ∀ a → ∃ λ aᴰ → ∀ bᴰ → Tm _ (Aᴰ a .₂ aᴰ .₂ bᴰ .₂)

infix 6 _[_]T
_[_]T : ∀ {Γ Δ} → Ty Δ → Sub Γ Δ → Ty Γ
_[_]T {next A f} {next A' f'} B σ =
    λ a →  B (σ a .₁) .₁
  , λ aᴰ → B (σ a .₁) .₂ aᴰ .₁
  , λ bᴰ → σ a .₂ (B (σ a .₁) .₂ aᴰ .₂ bᴰ .₁) .₁
  , B (σ a .₁) .₂ aᴰ .₂ bᴰ .₂ [ σ a .₂ _ .₂ ]T

infix 6 _[_]t
_[_]t : ∀ {Γ Δ A} → Tm Δ A → (σ : Sub Γ Δ) → Tm Γ (A [ σ ]T)
_[_]t {next A f} {next A' f'} {B} t σ =
    λ a → t (σ a .₁) .₁
  , λ bᴰ → t (σ a .₁) .₂ bᴰ [ σ a .₂ _ .₂ ]t

infixr 4 _*_
_*_ : Con → Con → Con
next A f * next A' f' =
    next (A × A') λ a → (f (a .₁) .₁ ⊎ f' (a .₂) .₁)
  , case (λ b  → f (a .₁) .₂ b * next A' f')
         (λ b' → next A f * f' (a .₂) .₂ b')

Proj1 : ∀ {Γ Δ} → Sub (Γ * Δ) Γ
Proj1 {next A B} {next A' B'} (a , a') = a , λ b → inj₁ b , Proj1

infixr 4 _+_
_+_ : Con → Con → Con
next A B + next A' B' = next (A ⊎ A')
  (case (λ a  → (B a .₁)   , λ b  → B a .₂ b + next A' B')
        (λ a' → (B' a' .₁) , λ b' → next A B + B' a' .₂ b'))

Inj1 : ∀ {Γ Δ} → Sub Γ (Γ + Δ)
Inj1 {next A B} {next A' B'} a = inj₁ a , λ b → b , Inj1

infixl 3 _▶_
_▶_ : (Γ : Con) → Ty Γ → Con
next A B ▶ T =
  next (Σ A (λ a → T a .₁)) λ {(a , aᴰ) → (B a .₁ ⊎ T a .₂ aᴰ .₁)
  , case (λ b  → B a .₂ b ▶ {!!})
         (λ bᴰ → B a .₂ (T a .₂ aᴰ .₂ bᴰ .₁) ▶ T a .₂ aᴰ .₂ bᴰ .₂)}

p : ∀ {Γ A} → Sub (Γ ▶ A) Γ
p {next A B} {T} (a , aᴰ) = a , λ b → (inj₁ b) , p

Ty' : Con → Set
Ty' (next A B) = ∀ a → (∀ b → Ty' (B a .₂ b) → Set) → Set

infix 6 _[_]T'
_[_]T' : ∀ {Γ Δ} → Ty' Δ → Sub Γ Δ → Ty' Γ
_[_]T' {next A B} {next A' B'} T σ =
  λ a P → T (σ a .₁) (λ b' T' → P (σ a .₂ b' .₁) (T' [ σ a .₂ b' .₂ ]T'))

infixl 3 _▶'_
_▶'_ : (Γ : Con) → Ty' Γ → Con
next A B ▶' T = next (Σ A λ a → ∃ (T a)) λ {(a , P , foo) → {!!}}



-- q : ∀ {Γ A} → Tm (Γ ▶ A) (A [ p ]T)
-- q {next A B} {T} (a , aᴰ) = aᴰ , λ bᴰ → {!!}


-- ------------------------------------------------------------

-- Conᴹ : Con → Set
-- Conᴹ (next A B f) = ∃ λ a → ∀ b → Conᴹ (f a b)

-- Subᴹ : ∀ {Γ Δ} → Sub Γ Δ → Conᴹ Γ → Conᴹ Δ
-- Subᴹ {next A B f} {next A' B' f'} (Aᴹ , Bᴹ , fᴹ) (a , step)
--   = (Aᴹ a) , λ b' → Subᴹ (fᴹ a b') (step (Bᴹ _ b'))
