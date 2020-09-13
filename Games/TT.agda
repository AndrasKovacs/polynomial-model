
{-# OPTIONS --type-in-type --postfix-projections #-}

module Games.TT where
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
    M    : M Γ → M Δ
    next : ∀ γ → Sub (next Δ (M γ)) (next Γ γ)
open Sub

id : ∀ {Γ} → Sub Γ Γ
id {Γ} .M    γ = γ
id {Γ} .next γ = id {Γ .next γ}

infixr 5 _∘_
_∘_ : ∀ {Γ Δ Ξ} → Sub Δ Ξ → Sub Γ Δ → Sub Γ Ξ
(σ ∘ δ) .M    m = σ .M (δ .M m)
(σ ∘ δ) .next m = δ .next m ∘ σ .next (δ .M m)

infixr 4 _+_
_+_ : Con → Con → Con
(Γ + Δ) .M    = Γ .M ⊎ Δ .M
(Γ + Δ) .next = case (Γ .next) (Δ .next)

Inj₁ : ∀ {Γ Δ} → Sub Γ (Γ + Δ)
Inj₁ .M    γ = inj₁ γ
Inj₁ .next γ = id

Inj₂ : ∀ {Γ Δ} → Sub Δ (Γ + Δ)
Inj₂ .M    δ = inj₂ δ
Inj₂ .next δ = id

+-rec : ∀ {Γ Δ Ξ} → Sub Γ Ξ → Sub Δ Ξ → Sub (Γ + Δ) Ξ
+-rec σ δ .M    = case (σ .M) (δ .M)
+-rec σ δ .next = ⊎-elim _ (σ .next) (δ .next)

⊘ : Con
⊘ .M    = ⊥
⊘ .next ()

init : ∀ {Γ} → Sub ⊘ Γ
init .M  ()
init .next ()

∙ : Con
∙ .M      = ⊤
∙ .next _ = ⊘

ε : ∀ {Γ} → Sub Γ ∙
ε .M    _ = _
ε .next _ = init

Ty : Con → Set
Ty Γ = Γ .M → Con

infix 6 _[_]T
_[_]T : ∀ {Γ Δ} → Ty Δ → Sub Γ Δ → Ty Γ
(A [ σ ]T) γ = A (σ .M γ)

[id]T : ∀ {Γ}{A : Ty Γ} → A [ id {Γ} ]T ≡ A
[id]T = refl

[∘]T : ∀ {Γ Δ Σ}{A : Ty Σ}{σ : Sub Δ Σ}{δ : Sub Γ Δ} → A [ σ ]T [ δ ]T ≡ A [ σ ∘ δ ]T
[∘]T = refl

record Tm (Γ : Con)(A : Ty Γ) : Set where
  constructor tm
  field
    M    : ∀ γ → M (A γ)
    next : ∀ γ → Sub (A γ .next (M γ)) (Γ .next γ)
open Tm

infix 6 _[_]t
_[_]t : ∀ {Γ Δ A}(t : Tm Δ A)(σ : Sub Γ Δ) → Tm Γ (A [ σ ]T)
(t [ σ ]t) .M    γ = t .M (σ .M γ)
(t [ σ ]t) .next γ = σ .next γ ∘ t .next (σ .M γ)

infixl 3 _▶_
_▶_ : (Γ : Con) → Ty Γ → Con
(Γ ▶ A) .M            = ∃ λ γ → A γ .M
(Γ ▶ A) .next (γ , α) = Γ .next γ + A _ .next α

p : ∀ {Γ A} → Sub (Γ ▶ A) Γ
p .M    (γ , α) = γ
p .next (γ , α) = Inj₁

q : ∀ {Γ A} → Tm (Γ ▶ A) (A [ p {Γ}{A} ]T)
q .M    (γ , α) = α
q .next (γ , α) = Inj₂

infixl 3 _,ₛ_
_,ₛ_ : ∀ {Γ Δ A}(σ : Sub Γ Δ) → Tm Γ (A [ σ ]T) → Sub Γ (Δ ▶ A)
(σ ,ₛ t) .M    γ = (σ .M γ) , (t .M γ)
(σ ,ₛ t) .next γ = +-rec (σ .next γ) (t .next γ)


-- Tensor product (symmetric monoidal)
--------------------------------------------------------------------------------

infixr 4 _⊗_
_⊗_ : Con → Con → Con
(Γ ⊗ Δ) .M                            = Γ .M × Δ .M
(Γ ⊗ Δ) .next (γ , δ) .M              = Γ .next γ .M ⊎ Δ .next δ .M
(Γ ⊗ Δ) .next (γ , δ) .next (inj₁ γ') = Γ .next γ .next γ' ⊗ Δ
(Γ ⊗ Δ) .next (γ , δ) .next (inj₂ δ') = Γ ⊗ Δ .next δ .next δ'

⊗-map : ∀ {Γ Γ' Δ Δ'} → Sub Γ Γ' → Sub Δ Δ' → Sub (Γ ⊗ Δ) (Γ' ⊗ Δ')
⊗-map f g .M    (γ , δ)                 = (f .M γ) , (g .M δ)
⊗-map f g .next (γ , δ) .M    (inj₁ γ') = inj₁ (f .next γ .M γ')
⊗-map f g .next (γ , δ) .M    (inj₂ δ') = inj₂ (g .next δ .M δ')
⊗-map f g .next (γ , δ) .next (inj₁ γ') = ⊗-map (f .next γ .next γ') g
⊗-map f g .next (γ , δ) .next (inj₂ δ') = ⊗-map f (g .next δ .next δ')

-- + functor action on id, ∘

⊗-idl→ : ∀ {Γ} → Sub (Γ ⊗ ∙) Γ
⊗-idl→ .M    (γ , _)          = γ
⊗-idl→ .next (γ , _) .M    γ' = inj₁ γ'
⊗-idl→ .next (γ , _) .next γ' = ⊗-idl→

⊗-idl← : ∀ {Γ} → Sub Γ (Γ ⊗ ∙)
⊗-idl← .M    γ                 = γ , tt
⊗-idl← .next γ .M    (inj₁ γ') = γ'
⊗-idl← .next γ .next (inj₁ γ') = ⊗-idl←

-- ⊗-idr→ : ∀ {Γ} → Sub (∙ ⊗ Γ) Γ
-- ⊗-idr← : ∀ {Γ} → Sub Γ (∙ ⊗ Γ)

⊗-ass→ : ∀ {Γ Δ Ξ} → Sub ((Γ ⊗ Δ) ⊗ Ξ) (Γ ⊗ Δ ⊗ Ξ)
⊗-ass→ .M    ((γ , δ) , ξ)                        = γ , δ , ξ
⊗-ass→ .next ((γ , δ) , ξ) .M    (inj₁ γ')        = inj₁ (inj₁ γ')
⊗-ass→ .next ((γ , δ) , ξ) .M    (inj₂ (inj₁ δ')) = inj₁ (inj₂ δ')
⊗-ass→ .next ((γ , δ) , ξ) .M    (inj₂ (inj₂ ξ')) = inj₂ ξ'
⊗-ass→ .next ((γ , δ) , ξ) .next (inj₁ γ')        = ⊗-ass→
⊗-ass→ .next ((γ , δ) , ξ) .next (inj₂ (inj₁ δ')) = ⊗-ass→
⊗-ass→ .next ((γ , δ) , ξ) .next (inj₂ (inj₂ ξ')) = ⊗-ass→

-- ⊗-ass← : ∀ {Γ Δ Ξ} → Sub (Γ ⊗ Δ ⊗ Ξ) ((Γ ⊗ Δ) ⊗ Ξ)
-- etc...

⊗-comm : ∀ {Γ Δ} → Sub (Γ ⊗ Δ) (Δ ⊗ Γ)
⊗-comm .M    (γ , δ)                 = δ , γ
⊗-comm .next (γ , δ) .M    (inj₁ γ') = inj₂ γ'
⊗-comm .next (γ , δ) .M    (inj₂ δ') = inj₁ δ'
⊗-comm .next (γ , δ) .next (inj₁ γ') = ⊗-comm
⊗-comm .next (γ , δ) .next (inj₂ δ') = ⊗-comm

-- + all naturalities, coherences


-- Pi
--------------------------------------------------------------------------------

Π : ∀ {Γ}(A : Ty Γ) → Ty (Γ ▶ A) → Ty Γ
Π A B γ .M                         = Tm (send (A γ .M) λ α → ∙ + A γ .next α) (λ α → B (γ , α))
Π A B γ .next t .M                 = ∃₂ λ α β' → isLeft (t .next α .M β')
Π A B γ .next t .next (α , β' , p) = B (γ , α) .next (t .M α) .next β'

Lam : ∀ {Γ A B} → Tm (Γ ▶ A) B → Tm Γ (Π {Γ} A B)
Lam t .M γ .M    α       = t .M (γ , α)
Lam t .M γ .next α .M β' = lmap (t .next (γ , α) .M β') _
Lam t .M γ .next α .next β' with t .next (γ , α) .M β' | t .next (γ , α) .next β'
... | inj₁ γ' | t' = init
... | inj₂ α' | t' = t'
Lam t .next γ .M (α , β' , p) with t .next (γ , α) .M β'
... | inj₁ γ' = γ'
... | inj₂ α' = ⊥-elim p
Lam t .next γ .next (α , β' , p) with t .next (γ , α) .M β' | t .next (γ , α) .next β'
... | inj₁ γ' | t' = t'
... | inj₂ α' | t' = ⊥-elim p

App : ∀ {Γ A B} → Tm Γ (Π {Γ} A B) → Tm (Γ ▶ A) B
App t .M    (γ , α) = t .M γ .M α
App t .next (γ , α) .M    β' with t .M γ .next α .M β' | inspect (t .M γ .next α .M) β'
                                | t .M γ .next α .next β'
... | inj₁ tt | [ eq ] | t' = inj₁ (t .next γ .M (α , β' , tr isLeft (eq ⁻¹) tt))
... | inj₂ α' | [ eq ] | t' = inj₂ α'
App t .next (γ , α) .next β' with t .M γ .next α .M β' | inspect (t .M γ .next α .M) β'
                                | t .M γ .next α .next β'
... | inj₁ tt | [ eq ] | t' = t .next γ .next _
... | inj₂ α' | [ eq ] | t' = t'


-- Sigma
--------------------------------------------------------------------------------

Sg : ∀ {Γ}(A : Ty Γ) → Ty (Γ ▶ A) → Ty Γ
Sg A B γ .M            = Σ (A γ .M) λ α → B (γ , α) .M
Sg A B γ .next (α , β) = A γ .next α + B (γ , α) .next β

Proj₁ : ∀ {Γ A B} → Tm Γ (Sg {Γ} A B) → Tm Γ A
Proj₁ t .M    γ = t .M γ .₁
Proj₁ t .next γ = t .next γ ∘ Inj₁

Proj₂ : ∀ {Γ A B}(t : Tm Γ (Sg {Γ} A B)) → Tm Γ (B [ id ,ₛ Proj₁ t ]T)
Proj₂ t .M    γ = t .M γ .₂
Proj₂ t .next γ = t .next γ ∘ Inj₂

Pair : ∀ {Γ A B}(t : Tm Γ A) → Tm Γ (B [ id ,ₛ t ]T) → Tm Γ (Sg {Γ} A B)
Pair t u .M    γ = (t .M γ) , (u .M γ)
Pair t u .next γ = +-rec (t .next γ) (u .next γ)


-- Universe
--------------------------------------------------------------------------------

U : ∀ {Γ} → Ty Γ
U γ .M      = Con
U γ .next _ = ⊘

El : ∀ {Γ} → Tm Γ (U {Γ}) → Ty Γ
El a γ .M    = a .M γ .M
El a γ .next = a .M γ .next

code : ∀ {Γ} → Ty Γ → Tm Γ (U {Γ})
code A .M    γ = A γ
code A .next γ = init

-- Identity
--------------------------------------------------------------------------------

Id : ∀ {Γ A} → Tm Γ A → Tm Γ A → Ty Γ
Id {Γ}{A} t u γ .M      = t .M γ ≡ u .M γ
Id {Γ}{A} t u γ .next p = ⊘

Refl : ∀ {Γ A}(t : Tm Γ A) → Tm Γ (Id t t)
Refl t .M    γ = refl
Refl t .next γ = init

UIP' : ∀ {Γ A}{t u : Tm Γ A}{e e' : Tm Γ (Id t u)} → Tm Γ (Id e e')
UIP' .M    γ = UIP _ _
UIP' .next γ = init

Tr : ∀ {Γ A}(B : Ty (Γ ▶ A)){t u : Tm Γ A}(e : Tm Γ (Id t u))
     → Tm Γ (B [ id ,ₛ t ]T) → Tm Γ (B [ id ,ₛ u ]T)
Tr {Γ} {A} B {t} {u} e bt .M    γ = tr (λ x → M (B (γ , x))) (e .M γ) (bt .M γ)
Tr {Γ} {A} B {t} {u} e bt .next γ =
  J (λ uγ eq → Sub (B (γ , uγ) .next (tr (λ x → M (B (γ , x))) eq (bt .M γ)))
                   (Γ .next γ))
    (e .M γ) (bt .next γ)

¬FunExt : (∀ {Γ A B}{t u : Tm Γ (Π {Γ} A B)} → Tm (Γ ▶ A) (Id (App t) (App u)) → Tm Γ (Id t u))
        → ⊥
¬FunExt fext with
  ap (λ t → t .next _ .M _)
  (fext {∙}{λ _ → send ⊤ λ _ → send Bool λ _ → ⊘}
          {λ _ → send ⊤ λ _ → send ⊤ λ _ → ⊘}
          {tm (λ _ → tm _ (λ _ → sub (λ _ → inj₂ true) λ _ → init))
               λ _ → sub (λ ()) λ ()}
          {tm (λ _ → tm _ (λ _ → sub (λ _ → inj₂ false) λ _ → init))
               λ _ → sub (λ ()) λ ()}
          (tm (λ _ → refl) λ _ → init)
          .M _)
... | ()

-- But note that since (Reflect -> FunExt), we have (¬Funext -> ¬Reflect) anyway
¬Reflect : (∀ {Γ A t u} → Tm Γ (Id {Γ}{A} t u) → t ≡ u) → ⊥
¬Reflect rf with
    ap (λ t → t .next _ . M _)
    (rf {send ⊤ λ _ → send Bool λ _ → ⊘}
        {λ _ → send ⊤ λ _ → ∙}
        {tm _ λ _ → sub (λ _ → true) λ _ → init}
        {tm _ λ _ → sub (λ _ → false) λ _ → init}
        (tm (λ _ → refl) λ _ → init))
... | ()


-- Nat
--------------------------------------------------------------------------------

Nat : ∀ {Γ} → Ty Γ
Nat γ .M      = ℕ
Nat γ .next _ = ⊘

Zero : ∀ {Γ} → Tm Γ (Nat {Γ})
Zero .M    _ = zero
Zero .next γ = init

Suc : ∀ {Γ} → Tm Γ (Nat {Γ}) → Tm Γ (Nat {Γ})
Suc t .M    γ = suc (t .M γ)
Suc t .next γ = init

NatElim : ∀ {Γ}(B : Ty (Γ ▶ Nat {Γ}))
          → Tm Γ (B [ id ,ₛ Zero {Γ} ]T)
          → Tm (Γ ▶ Nat {Γ} ▶ B) (λ {((γ , n) , bn) → B (γ , suc n)})
          → Tm (Γ ▶ Nat {Γ}) B
NatElim B z s .M    (γ , zero)  = z .M γ
NatElim B z s .M    (γ , suc n) = s .M ((γ , n) , NatElim B z s .M (γ , n))
NatElim B z s .next (γ , zero)  = Inj₁ ∘ z .next γ
NatElim B z s .next (γ , suc n) = +-rec id (NatElim B z s .next (γ , n)) ∘ s .next ((γ , n), _)
