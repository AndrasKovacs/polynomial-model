
{-# OPTIONS --type-in-type --rewriting --postfix-projections #-}

module Games.STT where

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
    Q    : Q Γ → Q Δ
    A    : ∀ {q} → A Δ (Q q) → A Γ q
    step : ∀ {q} a → Sub (step Γ {q} (A a)) (step Δ a)
open Sub

Ty : Set
Ty = Con

Tm : Con → Ty → Set
Tm = Sub

∙ : Con
∙ = game ⊤ (λ _ → ⊥) (λ ())

ε : ∀ {Γ} → Sub Γ ∙
ε = sub _ (λ ()) (λ ())

id : ∀ {Γ} → Sub Γ Γ
id {game Q A step} =
  sub (λ q → q) (λ a → a) (λ a → id)

infixr 5 _∘_
_∘_ : ∀ {Γ Δ Ξ} → Sub Δ Ξ → Sub Γ Δ → Sub Γ Ξ
_∘_ {game Q A step} {game Q' A' step'} {game Q'' A'' step''} σ δ =
  sub (λ q   → Sub.Q σ (Sub.Q δ q))
      (λ a'' → Sub.A δ (Sub.A σ a''))
      (λ a'' → Sub.step σ a'' ∘ Sub.step δ (Sub.A σ a''))

record Conᴹ (Γ : Con) : Set where
  inductive
  constructor conᴹ
  field
    asks  : Q Γ
    next  : ∀ a → Conᴹ (step Γ {asks} a)
open Conᴹ

Subᴹ : ∀ {Γ Δ} → Sub Γ Δ → Conᴹ Γ → Conᴹ Δ
Subᴹ σ (conᴹ asks next) =
  conᴹ (Q σ asks) (λ a → Subᴹ (step σ a) (next (A σ a)))

skip : ∀ {Γ}(Pl : Conᴹ Γ) → (a : A Γ (asks Pl)) → Conᴹ (step Γ a)
skip {Γ} (conᴹ asks next) a = next a

-- Conᴹ : Con → Set
-- Conᴹ (game Q A step) = ∃ λ q → ∀ a → Conᴹ (step {q} a)

-- skip : ∀ {Γ q a} → Conᴹ Γ → Conᴹ (step Γ {q} a)
-- skip {game Q A step} {q} {a} (q' , next) = {!next !}

-- skip : ∀ Γ q (a : A Γ q)(f : Q Γ → Q (step Γ a)) → (∀ {q} → A (step Γ a) (f q) → A Γ q) → Sub Γ (step Γ a)
-- skip (game Q A step) q a f g =
--   sub f g (λ {q'} a' → {!!})

infix 3 _<_ _≤_
_<_ _≤_ : Con → Con → Set
Γ ≤ Δ             = Γ ≡ Δ ⊎ Γ < Δ
Γ < game Q A step = ∃₂ λ q (a : A q) → Γ ≤ step a


-- delay : ∀ {Γ Δ} → Γ < Δ → Sub Δ Γ
-- delay {Γ} {game Q A step} (q , a , inj₁ refl) =
--   {!!}
-- delay {Γ} {game Q A step} (q , a , inj₂ p) =
--   sub {!!} {!!} {!!}

infixr 4 _+_
_+_ : Con → Con → Con
game Q A step + game Q' A' step' =
  game (Q ⊎ Q')
       (case A A')
       (λ {q} → ⊎-elim (λ q → case A A' q → Con)
                       (λ q a   → step a + game Q' A' step')
                       (λ q' a' → game Q A step + step' a')
                       q)

Inj₁ : ∀ {Γ Δ} → Sub Γ (Γ + Δ)
Inj₁ {game Q A step} {game Q' A' step'} =
  sub inj₁ (λ a → a) λ {q} a → Inj₁

Inj₂ : ∀ {Γ Δ} → Sub Δ (Γ + Δ)
Inj₂ {game Q A step} {game Q' A' step'} =
  sub inj₂ (λ a' → a') λ {q'} a' → Inj₂ {game Q A step}{step' a'}

Either : ∀ {Γ Δ Ξ} → Sub Γ Ξ → Sub Δ Ξ → Sub (Γ + Δ) Ξ
Either {game Q A step} {game Q' A' step'} {game Q'' A'' step''} σ t =
  sub (case (Sub.Q σ) (Sub.Q t))
      (λ {q} → ⊎-elim (λ q → A'' (case (Sub.Q σ) (Sub.Q t) q) → case A A' q)
                      (λ _ → Sub.A σ)
                      (λ _ → Sub.A t) q)
      λ { {inj₁ q}  a'' → Either (Sub.step σ a'') {!!}
        ; {inj₂ q'} a'' → Either {!!} (Sub.step t a'')}

infixl 3 _▶_
_▶_ : Con → Ty → Con
Γ@(game Q A step) ▶ B@(game Q' A' step') =
  game (Q × Q')
       (λ qq' → A (qq' .₁) ⊎ A' (qq' .₂))
       (case (λ a → step a ▶ B) (λ a' → Γ ▶ step' a'))

p : ∀ {Γ B} → Sub (Γ ▶ B) Γ
p {game _ _ _} {game _ _ _} = sub ₁ inj₁ λ _ → p

q : ∀ {Γ B} → Tm (Γ ▶ B) B
q Γ@{game _ _ _} {game _ _ _} = sub ₂ inj₂ λ a' → q {Γ}



-- problem: we can only take tail of a Sub in *lockstep*!
-- no way to recurse in _,ₛ_!!! We don't even have a weak product yet!
infixl 3 _,ₛ_
_,ₛ_ : ∀ {Γ Δ B} → Sub Γ Δ → Tm Γ B → Sub Γ (Δ ▶ B)
_,ₛ_ {game Q A step} {game Q' A' step'} {game Q'' A'' step''} σ t =
  sub (λ q → Sub.Q σ q , Sub.Q t q)
      (case (Sub.A σ)
            (Sub.A t))
      (λ {q} → ⊎-elim _
            (λ a   → Sub.step σ a ,ₛ {!t!})
            (λ a'' →
               _,ₛ_ {_}{game Q' A' step'}{step'' a''}
                    {!!}
                    (Sub.step t a'')))



-- -- infixr 4 _*_
-- -- _*_ : Con → Con → Con
-- -- next A f * next A' f' =
-- --     next (A × A') λ a → (f (a .₁) .₁ ⊎ f' (a .₂) .₁)
-- --   , case (λ b  → f (a .₁) .₂ b * next A' f')
-- --          (λ b' → next A f * f' (a .₂) .₂ b')







-- data Con : Set where
--   next : (A : Set)(B : A → ∃ λ B → B → Con) → Con

-- Sub : Con → Con → Set
-- Sub (next A f) (next A' f') =
--   ∀ a → ∃ λ a' → ∀ b' → ∃ λ b → Sub (f a .₂ b) (f' a' .₂ b')

-- infixr 5 _∘_
-- _∘_ : ∀ {Γ Δ Ξ} → Sub Δ Ξ → Sub Γ Δ → Sub Γ Ξ
-- _∘_ {next A f} {next A' f'} {next A'' f''} σ δ =
--     λ a   → (σ (δ a .₁) .₁)
--   , λ b'' → δ a .₂ (σ (δ a .₁) .₂ b'' .₁) .₁
--   , σ (δ a .₁) .₂ b'' .₂ ∘ δ a .₂ (σ (δ a .₁) .₂ b'' .₁) .₂

-- id : ∀ {Γ} → Sub Γ Γ
-- id {next A f} = λ a → a , λ b' → b' , id

-- ∙ : Con
-- ∙ = next ⊤ λ _ → ⊥ , λ ()

-- ε : ∀ {Γ} → Sub Γ ∙
-- ε {next A f} a = tt , (λ ())

-- Bot : Con
-- Bot = next ⊥ λ ()

-- Bot-Init : ∀ {Γ} → Sub Bot Γ
-- Bot-Init {next A f} ()

-- -- Aᴰ   : A → Set
-- -- Bᴰ   : ∀ a aᴰ → B a → Set
-- -- next : ∀ a aᴰ b → Bᴰ a aᴰ b → Ty (B a b)

-- -- ToIx (Bᴰ, base) = λ b. ∃ bᴰ. base bᴰ ≡ b

-- -- Aᴰ   : A → Set
-- -- Bᴰ   : ∀ a aᴰ → ∃ Bᴰ. Bᴰ → B a
-- -- next : ∀ a aᴰ b → Bᴰ a aᴰ b → Ty (B a b)

-- -- Aᴰ   : A → Set
-- -- Bᴰ   : ∀ a aᴰ → ∃ Bᴰ. Bᴰ → B a
-- -- next : ∀ a aᴰ b → (∃ bᴰ. Bᴰ a aᴰ .₂ bᴰ ≡ b) → Ty (B a b)

-- -- Aᴰ   : A → Set
-- -- Bᴰ   : ∀ a aᴰ → ∃ Bᴰ. Bᴰ → B a
-- -- next : ∀ a aᴰ bᴰ → Ty (B a (Bᴰ a aᴰ .₂ bᴰ))





-- -- Ty : Con → Set
-- -- Ty (next A B) =
-- --   ∀ a → ∃ λ Aᴰ → Aᴰ → ∃ λ Bᴰ → Bᴰ → ∃ λ b → Ty (B a .₂ b)





-- -- Tm : ∀ Γ → Ty Γ → Set
-- -- Tm (next A f) Aᴰ = ∀ a → ∃ λ aᴰ → ∀ bᴰ → Tm _ (Aᴰ a .₂ aᴰ .₂ bᴰ .₂)

-- -- infix 6 _[_]T
-- -- _[_]T : ∀ {Γ Δ} → Ty Δ → Sub Γ Δ → Ty Γ
-- -- _[_]T {next A f} {next A' f'} B σ =
-- --     λ a →  B (σ a .₁) .₁
-- --   , λ aᴰ → B (σ a .₁) .₂ aᴰ .₁
-- --   , λ bᴰ → σ a .₂ (B (σ a .₁) .₂ aᴰ .₂ bᴰ .₁) .₁
-- --   , B (σ a .₁) .₂ aᴰ .₂ bᴰ .₂ [ σ a .₂ _ .₂ ]T

-- -- infix 6 _[_]t
-- -- _[_]t : ∀ {Γ Δ A} → Tm Δ A → (σ : Sub Γ Δ) → Tm Γ (A [ σ ]T)
-- -- _[_]t {next A f} {next A' f'} {B} t σ =
-- --     λ a → t (σ a .₁) .₁
-- --   , λ bᴰ → t (σ a .₁) .₂ bᴰ [ σ a .₂ _ .₂ ]t

-- -- infixr 4 _*_
-- -- _*_ : Con → Con → Con
-- -- next A f * next A' f' =
-- --     next (A × A') λ a → (f (a .₁) .₁ ⊎ f' (a .₂) .₁)
-- --   , case (λ b  → f (a .₁) .₂ b * next A' f')
-- --          (λ b' → next A f * f' (a .₂) .₂ b')

-- -- Proj1 : ∀ {Γ Δ} → Sub (Γ * Δ) Γ
-- -- Proj1 {next A B} {next A' B'} (a , a') = a , λ b → inj₁ b , Proj1

-- -- infixr 4 _+_
-- -- _+_ : Con → Con → Con
-- -- next A B + next A' B' = next (A ⊎ A')
-- --   (case (λ a  → (B a .₁)   , λ b  → B a .₂ b + next A' B')
-- --         (λ a' → (B' a' .₁) , λ b' → next A B + B' a' .₂ b'))

-- -- Inj1 : ∀ {Γ Δ} → Sub Γ (Γ + Δ)
-- -- Inj1 {next A B} {next A' B'} a = inj₁ a , λ b → b , Inj1

-- -- infixl 3 _▶_
-- -- _▶_ : (Γ : Con) → Ty Γ → Con
-- -- next A B ▶ T =
-- --   next (Σ A (λ a → T a .₁)) λ {(a , aᴰ) → (B a .₁ ⊎ T a .₂ aᴰ .₁)
-- --   , case (λ b  → B a .₂ b ▶ {!T a .₂ aᴰ .₂ ? .₂!})
-- --          (λ bᴰ → B a .₂ (T a .₂ aᴰ .₂ bᴰ .₁) ▶ T a .₂ aᴰ .₂ bᴰ .₂)}

-- -- p : ∀ {Γ A} → Sub (Γ ▶ A) Γ
-- -- p {next A B} {T} (a , aᴰ) = a , λ b → (inj₁ b) , p



-- -- Ty' : Con → Set
-- -- Ty' (next A B) = ∀ a → (∀ b → Ty' (B a .₂ b) → Set) → Set

-- -- infix 6 _[_]T'
-- -- _[_]T' : ∀ {Γ Δ} → Ty' Δ → Sub Γ Δ → Ty' Γ
-- -- _[_]T' {next A B} {next A' B'} T σ =
-- --   λ a P → T (σ a .₁) (λ b' T' → P (σ a .₂ b' .₁) (T' [ σ a .₂ b' .₂ ]T'))

-- -- infixl 3 _▶'_
-- -- _▶'_ : (Γ : Con) → Ty' Γ → Con
-- -- next A B ▶' T = next (Σ A λ a → ∃ (T a)) λ {(a , P , foo) → {!!}}



-- -- -- q : ∀ {Γ A} → Tm (Γ ▶ A) (A [ p ]T)
-- -- -- q {next A B} {T} (a , aᴰ) = aᴰ , λ bᴰ → {!!}


-- -- -- ------------------------------------------------------------

-- -- -- Conᴹ : Con → Set
-- -- -- Conᴹ (next A B f) = ∃ λ a → ∀ b → Conᴹ (f a b)

-- -- -- Subᴹ : ∀ {Γ Δ} → Sub Γ Δ → Conᴹ Γ → Conᴹ Δ
-- -- -- Subᴹ {next A B f} {next A' B' f'} (Aᴹ , Bᴹ , fᴹ) (a , step)
-- -- --   = (Aᴹ a) , λ b' → Subᴹ (fᴹ a b') (step (Bᴹ _ b'))
