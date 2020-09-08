{-# OPTIONS --type-in-type --rewriting #-}

module Games.Notes where

open import Data.Unit
open import Data.Empty
open import Data.Product renaming (proj₁ to ₁; proj₂ to ₂)
open import Data.Bool
open import Relation.Binary.PropositionalEquality
  renaming (trans to infixr 4 _◾_; subst to tr; cong to ap; sym to infix 6 _⁻¹)
import Axiom.Extensionality.Propositional as Axiom
open import Function hiding (_∘_; id)

{-# BUILTIN REWRITE _≡_ #-}

coe : ∀ {i}{A B : Set i} → A ≡ B → A → B
coe refl x = x

postulate
  ext  : ∀ {i j} → Axiom.Extensionality i j
  exti : ∀ {i j} → Axiom.ExtensionalityImplicit i j

data Con : Set where
  next : (A : Set)(B : A → Set)(f : ∀ a → B a → Con) → Con

Sub : Con → Con → Set
Sub (next A B f) (next A' B' f') =
  ∃ λ (Aᴹ : A → A') →
  ∃ λ (Bᴹ : ∀ a → B' (Aᴹ a) → B a) →
  ∀ a b' → Sub (f a (Bᴹ a b')) (f' (Aᴹ a) b')

abstract
  Sub≡ : ∀ {A B f A' B' f' Aᴹ Bᴹ fᴹ Aᴹ' Bᴹ' fᴹ'}
         → (A≡ : ∀ a → Aᴹ a ≡ Aᴹ' a)
         → (B≡ : ∀ a b' → Bᴹ a b' ≡ Bᴹ' a (tr B' (A≡ a) b'))
         → (f≡ : ∀ a b' → fᴹ a b' ≡ {!!})
         → (Sub (next A B f) (next A' B' f') ∋ (Aᴹ  , Bᴹ  , fᴹ))
         ≡ (Sub (next A B f) (next A' B' f') ∋ (Aᴹ' , Bᴹ' , fᴹ'))
  Sub≡ = {!!}

infixr 5 _∘_
_∘_ : ∀ {Γ Δ Ξ} → Sub Δ Ξ → Sub Γ Δ → Sub Γ Ξ
_∘_ {next A B f} {next A' B' f'} {next A'' B'' f''} (Aᴹ , Bᴹ , fᴹ)(Aᴹ' , Bᴹ' , fᴹ') =
    (λ a → Aᴹ (Aᴹ' a))
  , (λ _ b'' → Bᴹ' _ (Bᴹ _ b''))
  , (λ a b'' → (fᴹ (Aᴹ' a) b'') ∘ (fᴹ' a (Bᴹ _ b'')))

id : ∀ {Γ} → Sub Γ Γ
id {next A B f} = (λ a → a) , (λ _ b → b) , λ a b → id {f a b}

∙ : Con
∙ = next ⊤ (λ _ → ⊥) (λ _ ())

ε : ∀ {Γ} → Sub Γ ∙
ε {next A B f} = _ , (λ _ ()) , (λ _ ())

postulate
  εη : ∀ {Γ}{σ : Sub Γ ∙} → σ ≡ ε
-- εη {next A B f} {Aᴹ , Bᴹ , fᴹ} = Sub≡ (λ _ → refl) (λ _ ()) (λ _ ())

Bot : Con
Bot = next ⊥ (λ ()) (λ ())

Bot-Init : ∀ {Γ} → Sub Bot Γ
Bot-Init {next A B f} = (λ ()) , (λ ()) , (λ ())

Ty : Con → Set
Ty (next A B f) =
  ∃ λ (Aᴰ : A → Set) →
  ∃ λ (Bᴰ : ∀ {a} → Aᴰ a → Set) →
      (∀ a (aᴰ : Aᴰ a) → Bᴰ aᴰ → ∃ λ b → Ty (f a b))

Ty' : Con → Set
Ty' (next A B f) =
  ∀ a → ∃ λ Aᴰ → Aᴰ → ∃ λ Bᴰ → Bᴰ → ∃ λ b → Ty (f a b)

infix 6 _[_]T
_[_]T : ∀ {Γ Δ} → Ty Δ → Sub Γ Δ → Ty Γ
_[_]T {next A B f} {next A' B' f'} (Aᴰ , Bᴰ , fᴰ) (Aᴹ , Bᴹ , fᴹ) =
    (λ a → Aᴰ (Aᴹ a))
  , (λ {a} aᴰ → Bᴰ {Aᴹ a} aᴰ)
  , (λ a aᴰ bᴰ → _ , fᴰ (Aᴹ a) aᴰ bᴰ .₂ [ fᴹ a _ ]T)

Tm : ∀ Γ → Ty Γ → Set
Tm (next A B f) (Aᴰ , Bᴰ , fᴰ) =
  ∃ λ (Aˢ : ∀ a → Aᴰ a) →
  ∀ (a : A) bᴰ → Tm (f a (fᴰ a (Aˢ a) bᴰ .₁)) (fᴰ a (Aˢ a) bᴰ .₂)

infix 6 _[_]t
_[_]t : ∀ {Γ Δ A} → Tm Δ A → (σ : Sub Γ Δ) → Tm Γ (A [ σ ]T)
_[_]t {next A B f} {next A' B' f'} {Aᴰ , Bᴰ , fᴰ} (Aˢ , fˢ) (Aᴹ , Bᴹ , fᴹ) =
    (λ a → Aˢ (Aᴹ a))
  , (λ a bᴰ → fˢ (Aᴹ a) bᴰ [ fᴹ a (₁ (fᴰ (Aᴹ a) (Aˢ (Aᴹ a)) bᴰ)) ]t)

------------------------------------------------------------

Conᴹ : Con → Set
Conᴹ (next A B f) = ∃ λ a → ∀ b → Conᴹ (f a b)

Subᴹ : ∀ {Γ Δ} → Sub Γ Δ → Conᴹ Γ → Conᴹ Δ
Subᴹ {next A B f} {next A' B' f'} (Aᴹ , Bᴹ , fᴹ) (a , step)
  = (Aᴹ a) , λ b' → Subᴹ (fᴹ a b') (step (Bᴹ _ b'))
