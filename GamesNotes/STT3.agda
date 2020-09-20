
{-# OPTIONS --type-in-type --postfix-projections #-}

module Games.STT3 where

open import Lib

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
    step : ∀ {q} a' → Sub (step Γ {q} (A a')) (step Δ {Q q} a')
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

infixr 4 _*_
_*_ : Con → Con → Con
game Q A step * game Q' A' step' =
  game (Q × Q') (λ {(q , q') → A q ⊎ A' q'}) (case step step')

Proj1 : ∀ {Γ Δ} → Sub (Γ * Δ) Γ
Proj1 {game Q A step} {game Q' A' step'} = sub ₁ inj₁ (λ _ → id)

Proj2 : ∀ {Γ Δ} → Sub (Γ * Δ) Δ
Proj2 {game Q A step} {game Q' A' step'} = sub ₂ inj₂ (λ _ → id)

Pair : ∀ {Γ B C} → Sub Γ B → Sub Γ C → Sub Γ (B * C)
Pair {game Q A step} {game Q' A' step'}{game Q'' A'' step''} σ δ =
  sub (λ q → Sub.Q σ q , Sub.Q δ q)
      (λ { (inj₁ x) → Sub.A σ x ; (inj₂ y) → Sub.A δ y})
      (λ { (inj₁ x) → Sub.step σ x ; (inj₂ y) → Sub.step δ y})



infixr 3 _⇒_
_⇒_ : Con → Con → Con
game Q A step ⇒ game Q' A' step' =
  game ((q : Q) → ∃ λ q' → (a' : A' q') → ⊤ ⊎ Σ (A q) λ a → Sub (step a) (step' a'))
       (λ f → ∃₂ λ q a' → isLeft (f q .₂ a'))
       (λ { {f}(q , a' , p) → step' a'})

Lam : ∀ {Γ B C} → Sub (Γ * B) C → Sub Γ (B ⇒ C)
Lam {game Q A step} {game Q' A' step'} {game Q'' A'' step''} σ =
  sub (λ q q' → Sub.Q σ (q , q')
       , λ a'' → ⊎-elim (λ x → Sub (case step step' x) (step'' a'')
                              → ⊤ ⊎ Σ (A' q') (λ a → Sub (step' a) (step'' a'')))
                        (λ a σ → inj₁ tt)
                        (λ a' σ → inj₂ (a' , σ))
                        (Sub.A σ a'') (Sub.step σ a''))
      (λ { {q} (q' , a'' , p) →
               ⊎-elim (λ x →
                        (σ' : Sub (case step step' x) (step'' a''))
                        (p : isLeft (⊎-elim (λ x → Sub (case step step' x) (step'' a'') →
                             ⊤ ⊎ Σ (A' q') (λ a → Sub (step' a) (step'' a''))) (λ a σ₁ →
                             inj₁ tt) (λ a' σ₁ → inj₂ (a' , σ₁)) x σ'))
                         → A q)
                      (λ a _ _ → a)
                      (λ a' σ' ())
                      (Sub.A σ a'') (Sub.step σ a'') p
             })
      (λ { {q} (q' , a'' , p) →
             ⊎-elim (λ x → (σ' : Sub (case step step' x) (step'' a''))
                           (p : isLeft (⊎-elim (λ x → Sub (case step step' x) (step'' a'') →
                                ⊤ ⊎ Σ (A' q') (λ a → Sub (step' a) (step'' a''))) (λ a σ₁ →
                                inj₁ tt) (λ a' σ₁ → inj₂ (a' , σ₁)) x σ'))
                       →
                       Sub (step (⊎-elim (λ x → (σ' : Sub (case step step' x)
                       (step'' a'')) → isLeft (⊎-elim (λ x₁ → Sub (case step
                       step' x₁) (step'' a'') → ⊤ ⊎ Σ (A' q') (λ a → Sub (step'
                       a) (step'' a''))) (λ a σ₁ → inj₁ tt) (λ a' σ₁ → inj₂ (a'
                       , σ₁)) x σ') → A q) (λ a _ _ → a) (λ a' σ' ()) x σ' p))
                       (step'' a''))
                     (λ a σ' _ → σ')
                     (λ a' σ' ())
                     (Sub.A σ a'') (Sub.step σ a'') p
               })

App : ∀ {Γ B C} → Sub Γ (B ⇒ C) → Sub (Γ * B) C
App {game Q A step} {game Q' A' step'} {game Q'' A'' step''} σ =
  sub (λ {(q , q') → Sub.Q σ q q' .₁})
      (λ { {q , q'} a'' →
            ⊎-elim (λ x → (isLeft x → A q)
                        → A q ⊎ A' q')
                   (λ _ f → inj₁ (f _))
                   (λ {(a' , σ') f → inj₂ a'})
                   (Sub.Q σ q q' .₂ a'') (λ p → Sub.A σ {q} (q' , a'' , p))})
      λ { {q , q'} a'' →

      ⊎-elim (λ x → (x≡   : x ≡ Sub.Q σ q q' .₂ a'')
                    (foo  : isLeft x → A q)
                    (foo≡ : ∀ p → Sub.A σ (q' , a'' , p) ≡ foo (tr isLeft (x≡ ⁻¹) p))
                  →
             Sub
              (case step step'
               (⊎-elim (λ x → (isLeft x → A q) → A q ⊎ A' q')
                (λ _ f → inj₁ (f tt)) (λ { (a' , σ') f → inj₂ a' })
                x foo))
              (step'' a''))
          (λ _ x≡ foo foo≡ → tr (λ y → Sub (step y) (step'' a''))
                                (foo≡ (tr isLeft x≡ tt))
                                (Sub.step σ (q' , a'' , tr isLeft x≡ tt)))
          (λ {(a' , σ') _ _ _ → σ'})
          (Sub.Q σ q q' .₂ a'') refl (λ p → Sub.A σ (q' , a'' , p))
          (λ _ → refl)
          }
