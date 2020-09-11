
{-# OPTIONS --type-in-type --rewriting --postfix-projections #-}

module Games.STT2 where

open import Data.Unit using (tt; ⊤)
open import Data.Empty
open import Data.Product renaming (proj₁ to ₁; proj₂ to ₂)
open import Data.Bool using (true; false; Bool)
open import Relation.Binary.PropositionalEquality
  renaming (trans to infixr 4 _◾_; subst to tr; cong to ap; sym to infix 6 _⁻¹)
import Axiom.Extensionality.Propositional as Axiom
open import Function using (_∋_)
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

⊎-elim : ∀ {i j k}{A : Set i}{B : Set j}(P : A ⊎ B → Set k)
         → (∀ a → P (inj₁ a))
         → (∀ b → P (inj₂ b))
         → ∀ ab → P ab
⊎-elim P l r (inj₁ x) = l x
⊎-elim P l r (inj₂ y) = r y


-- Well-founded game model of simple type theory
--------------------------------------------------------------------------------

-- Well-founded game
record Con : Set where
  inductive
  constructor game
  field
    Q    : Set
    A    : Q → Set
    step : ∀ {q} → A q → Con
open Con

-- Game morphism
record Sub (Γ Δ : Con) : Set where
  inductive
  constructor sub
  field
    Q    : Q Δ → Q Γ
    A    : ∀ {q'} → A Γ (Q q') → A Δ q'
    step : ∀ {q'} a → Sub (step Γ {Q q'} a) (step Δ {q'} (A a))
open Sub

Ty : Set
Ty = Con

Tm : Con → Ty → Set
Tm = Sub

∙ : Con
∙ = game ⊥ (λ ()) λ { {()}}

ε : ∀ {Γ} → Sub Γ ∙
ε = sub (λ ()) (λ { {()}}) λ { {()}}

id : ∀ {Γ} → Sub Γ Γ
id {game Q A step} =
  sub (λ q → q) (λ a → a) (λ a → id)

infixr 5 _∘_
_∘_ : ∀ {Γ Δ Ξ} → Sub Δ Ξ → Sub Γ Δ → Sub Γ Ξ
_∘_ {game Q A step} {game Q' A' step'} {game Q'' A'' step''} σ δ =
  sub (λ q   → Sub.Q δ (Sub.Q σ q))
      (λ a'' → Sub.A σ (Sub.A δ a''))
      (λ a'' → Sub.step σ (Sub.A δ a'') ∘ Sub.step δ a'')

Conᴹ : Con → Set
Conᴹ (game Q A step) = ∀ q → ∃ λ a → Conᴹ (step {q} a)

Subᴹ : ∀ {Γ Δ} → Sub Γ Δ → Conᴹ Γ → Conᴹ Δ
Subᴹ {game Q A step} {game Q' A' step'} σ γ =
  λ q' → (Sub.A σ (γ (Sub.Q σ q') .₁)) , Subᴹ (Sub.step σ _) (γ (Sub.Q σ q') .₂)

infixr 4 _*_
_*_ : Con → Con → Con
game Q A step * game Q' A' step' =
  game (Q ⊎ Q') (case A A') (λ{ {inj₁ _} → step ; {inj₂ _} → step'})

Proj1 : ∀ {Γ Δ} → Sub (Γ * Δ) Γ
Proj1 {game Q A step} {game Q' A' step'} = sub inj₁ (λ a → a) λ _ → id

Proj2 : ∀ {Γ Δ} → Sub (Γ * Δ) Δ
Proj2 {game Q A step} {game Q' A' step'} = sub inj₂ (λ a → a) λ _ → id

Pair : ∀ {Γ B C} → Sub Γ B → Sub Γ C → Sub Γ (B * C)
Pair {game Q A step} {game Q' A' step'}{game Q'' A'' step''} σ δ =
  sub (case (Sub.Q σ) (Sub.Q δ))
      (λ { {inj₁ x} → Sub.A σ ; {inj₂ y} → Sub.A δ})
      (λ { {inj₁ x} → Sub.step σ ; {inj₂ y} → Sub.step δ})

infixr 4 _+_
_+_ : Con → Con → Con
game Q A step + game Q' A' step' =
  game (Q × Q') (λ {(q , q') → A q ⊎ A' q'})
       (λ { (inj₁ a ) → step a; (inj₂ a') → step' a'})

Inj1 : ∀ {Γ Δ} → Sub Γ (Γ + Δ)
Inj1 {game Q A step} {game Q' A' step'} = sub ₁ inj₁ λ _ → id

Inj2 : ∀ {Γ Δ} → Sub Δ (Γ + Δ)
Inj2 {game Q A step} {game Q' A' step'} = sub ₂ inj₂ λ _ → id

Either : ∀ {Γ B C} → Sub B Γ → Sub C Γ → Sub (B + C) Γ
Either {game Q A step} {game Q' A' step'}{game Q'' A'' step''} σ δ =
  sub (λ q → Sub.Q σ q , Sub.Q δ q)
      (case (Sub.A σ) (Sub.A δ))
      (λ { (inj₁ a') → Sub.step σ a' ; (inj₂ a) → Sub.step δ a})

Bot : Con
Bot = game ⊤ (λ _ → ⊥) λ ()

BotElim : ∀ {Γ} → Sub Bot Γ
BotElim {Γ} = sub _ (λ ()) (λ ())

-- Exponentials?
infixr 3 _⇒_
_⇒_ : Con → Con → Con
game Q A step ⇒ game Q' A' step' =
  game (∀ (q' : Q') → ∃ λ (q : Q) → A q → ⊤ ⊎ A' q')
       (λ f → ∃₂ λ (q' : Q')(a : A (f q' .₁)) → f q' .₂ a ≡ inj₁ tt)
       (λ { {f} (q' , a , p) → step {f q' .₁} a ⇒ step' {q'} {!f q' .₂ a!}})

App : ∀ {Γ B C} → Sub (Γ * B) C → Sub Γ (B ⇒ C)
App = {!!}
