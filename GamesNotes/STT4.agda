
{-# OPTIONS --type-in-type --postfix-projections #-}

module Games.STT4 where

open import Lib

-- Well-founded game model of simple type theory
--------------------------------------------------------------------------------

record Con : Set where
  inductive
  constructor send
  field
    Q    : Set
    step : Q → Con
open Con

record Sub (Γ Δ : Con) : Set where
  inductive
  constructor sub
  field
    Q    : Q Γ → Q Δ
    step : ∀ q → Sub (step Δ (Q q)) (step Γ q)
open Sub

id : ∀ {Γ} → Sub Γ Γ
id {send _ _} = sub (λ q → q) (λ _ → id)

infixr 5 _∘_
_∘_ : ∀ {Γ Δ Ξ} → Sub Δ Ξ → Sub Γ Δ → Sub Γ Ξ
_∘_ {send _ _} {send _ _} {send _ _} σ δ =
  sub (λ q → Sub.Q σ (Sub.Q δ q))
      (λ q → Sub.step δ q ∘ Sub.step σ (Sub.Q δ q))

Bot : Con
Bot = send ⊥ λ ()

Init : ∀ {Γ} → Sub Bot Γ
Init {Γ} = sub (λ ()) λ ()

Top : Con
Top = send ⊤ λ _ → Bot

Final : ∀ {Γ} → Sub Γ Top
Final = sub _ λ _ → Init

--------------------------------------------------------------------------------

Conᴬ : Con → Set
Conᴮ : Con → Set
Conᴬ (send Q step) = ∃ λ q → Conᴮ (step q)
Conᴮ (send Q step) = ∀ q → Conᴬ (step q)

Subᴬ : ∀ {Γ Δ} → Sub Γ Δ → Conᴬ Γ → Conᴬ Δ
Subᴮ : ∀ {Γ Δ} → Sub Δ Γ → Conᴮ Γ → Conᴮ Δ
Subᴬ {send _ _} {send _ _} σ (q , next) = Sub.Q σ q , Subᴮ (Sub.step σ q) next
Subᴮ {send _ _} {send _ _} σ γ q'       = Subᴬ (Sub.step σ q') (γ (Sub.Q σ q'))

--------------------------------------------------------------------------------

infixr 4 _+_
_+_ : Con → Con → Con
send Q step + send Q' step' = send (Q ⊎ Q') (case step step')

Inj₁ : ∀ {Γ Δ} → Sub Γ (Γ + Δ)
Inj₁ {send Q step} {send Q' step'} = sub inj₁ λ _ → id

Inj₂ : ∀ {Γ Δ} → Sub Δ (Γ + Δ)
Inj₂ {send Q step} {send Q' step'} = sub inj₂ λ _ → id

Copair : ∀ {Γ Δ Ξ} → Sub Γ Ξ → Sub Δ Ξ → Sub (Γ + Δ) Ξ
Copair {send Q step} {send Q' step'}{send Q'' step''} σ δ =
  sub (case (Sub.Q σ) (Sub.Q δ)) (⊎-elim _ (Sub.step σ) (Sub.step δ))

--------------------------------------------------------------------------------

infixl 4 _*_
_*_ : Con → Con → Con
send Q step * send Q' step' = send (Q × Q') λ {(q , q') → step q + step' q'}

Proj₁ : ∀ {Γ Δ} → Sub (Γ * Δ) Γ
Proj₁ {send Q step} {send Q' step'} = sub ₁ λ _ → Inj₁

Proj₂ : ∀ {Γ Δ} → Sub (Γ * Δ) Δ
Proj₂ {send Q step} {send Q' step'} = sub ₂ λ {(q , q') → Inj₂ {step q}}

Pair : ∀ {Γ Δ Ξ} → Sub Γ Δ → Sub Γ Ξ → Sub Γ (Δ * Ξ)
Pair {send Q step} {send Q' step'}{send Q'' step''} σ δ =
  sub (λ q → Sub.Q σ q , Sub.Q δ q) (λ q → Copair (Sub.step σ q) (Sub.step δ q))

--------------------------------------------------------------------------------

Q₂ : (Γ : Con) → Q Γ → Set
Q₂ Γ q = Q (step Γ q)

step₂ : (Γ : Con)(q : Q Γ)(a : Q₂ Γ q) → Con
step₂ Γ q = step (step Γ q)

MaybeStop : Con → Con
MaybeStop Γ = Top + Γ

infixr 3 _⇒_
_⇒_ : Con → Con → Con
Γ@(send _ _) ⇒ Δ@(send _ _) =
  send (Sub (send (Q Γ) λ q → Top + step Γ q) Δ) λ σ →
  send (∃₂ λ (q : Q Γ)(a' : Q₂ Δ (Q σ q)) → {!!})
  {!!}



-- infixr 3 _⇒_
-- _⇒_ : Con → Con → Con
-- Γ@(send _ _) ⇒ Δ@(send _ _) =
--   send (∀ q → ∃ λ q' → ∀ a' → ⊤ ⊎ ∃ λ a → Sub (step₂ Γ q a) (step₂ Δ q' a')) λ f →
--   send (∃₂ λ q a' → isLeft (f q .₂ a')) λ {(q , a' , _) →
--   step₂ Δ (f q .₁) a'}




-- infixr 3 _⇒_
-- _⇒_ : Con → Con → Con
-- send Q A step ⇒ send Q' A' step' =
--   send ((q : Q) → ∃ λ q' → (a' : A' q') → ⊤ ⊎ Σ (A q) λ a → Sub (step a) (step' a'))
--        (λ f → ∃₂ λ q a' → isLeft (f q .₂ a'))
--        (λ { {f}(q , a' , p) → step' a'})

-- Lam : ∀ {Γ B C} → Sub (Γ * B) C → Sub Γ (B ⇒ C)
-- Lam {send Q A step} {send Q' A' step'} {send Q'' A'' step''} σ =
--   sub (λ q q' → Sub.Q σ (q , q')
--        , λ a'' → ⊎-elim (λ x → Sub (case step step' x) (step'' a'')
--                               → ⊤ ⊎ Σ (A' q') (λ a → Sub (step' a) (step'' a'')))
--                         (λ a σ → inj₁ tt)
--                         (λ a' σ → inj₂ (a' , σ))
--                         (Sub.A σ a'') (Sub.step σ a''))
--       (λ { {q} (q' , a'' , p) →
--                ⊎-elim (λ x →
--                         (σ' : Sub (case step step' x) (step'' a''))
--                         (p : isLeft (⊎-elim (λ x → Sub (case step step' x) (step'' a'') →
--                              ⊤ ⊎ Σ (A' q') (λ a → Sub (step' a) (step'' a''))) (λ a σ₁ →
--                              inj₁ tt) (λ a' σ₁ → inj₂ (a' , σ₁)) x σ'))
--                          → A q)
--                       (λ a _ _ → a)
--                       (λ a' σ' ())
--                       (Sub.A σ a'') (Sub.step σ a'') p
--              })
--       (λ { {q} (q' , a'' , p) →
--              ⊎-elim (λ x → (σ' : Sub (case step step' x) (step'' a''))
--                            (p : isLeft (⊎-elim (λ x → Sub (case step step' x) (step'' a'') →
--                                 ⊤ ⊎ Σ (A' q') (λ a → Sub (step' a) (step'' a''))) (λ a σ₁ →
--                                 inj₁ tt) (λ a' σ₁ → inj₂ (a' , σ₁)) x σ'))
--                        →
--                        Sub (step (⊎-elim (λ x → (σ' : Sub (case step step' x)
--                        (step'' a'')) → isLeft (⊎-elim (λ x₁ → Sub (case step
--                        step' x₁) (step'' a'') → ⊤ ⊎ Σ (A' q') (λ a → Sub (step'
--                        a) (step'' a''))) (λ a σ₁ → inj₁ tt) (λ a' σ₁ → inj₂ (a'
--                        , σ₁)) x σ') → A q) (λ a _ _ → a) (λ a' σ' ()) x σ' p))
--                        (step'' a''))
--                      (λ a σ' _ → σ')
--                      (λ a' σ' ())
--                      (Sub.A σ a'') (Sub.step σ a'') p
--                })

-- App : ∀ {Γ B C} → Sub Γ (B ⇒ C) → Sub (Γ * B) C
-- App {send Q A step} {send Q' A' step'} {send Q'' A'' step''} σ =
--   sub (λ {(q , q') → Sub.Q σ q q' .₁})
--       (λ { {q , q'} a'' →
--             ⊎-elim (λ x → (isLeft x → A q)
--                         → A q ⊎ A' q')
--                    (λ _ f → inj₁ (f _))
--                    (λ {(a' , σ') f → inj₂ a'})
--                    (Sub.Q σ q q' .₂ a'') (λ p → Sub.A σ {q} (q' , a'' , p))})
--       λ { {q , q'} a'' →

--       ⊎-elim (λ x → (x≡   : x ≡ Sub.Q σ q q' .₂ a'')
--                     (foo  : isLeft x → A q)
--                     (foo≡ : ∀ p → Sub.A σ (q' , a'' , p) ≡ foo (tr isLeft (x≡ ⁻¹) p))
--                   →
--              Sub
--               (case step step'
--                (⊎-elim (λ x → (isLeft x → A q) → A q ⊎ A' q')
--                 (λ _ f → inj₁ (f tt)) (λ { (a' , σ') f → inj₂ a' })
--                 x foo))
--               (step'' a''))
--           (λ _ x≡ foo foo≡ → tr (λ y → Sub (step y) (step'' a''))
--                                 (foo≡ (tr isLeft x≡ tt))
--                                 (Sub.step σ (q' , a'' , tr isLeft x≡ tt)))
--           (λ {(a' , σ') _ _ _ → σ'})
--           (Sub.Q σ q q' .₂ a'') refl (λ p → Sub.A σ (q' , a'' , p))
--           (λ _ → refl)
--           }
