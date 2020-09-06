{-# OPTIONS --type-in-type #-}

module Lib where

open import Relation.Binary.PropositionalEquality
  renaming (trans to infixr 4 _◾_; subst to tr; cong to ap; sym to infix 6 _⁻¹)
  public
open import Data.Unit using (⊤; tt) public
open import Data.Empty public
open import Data.Product renaming (proj₁ to ₁; proj₂ to ₂) public
open import Function using (_∋_; case_of_) public
open import Level renaming (zero to lzero; suc to lsuc) public
open import Data.Sum using (_⊎_; inj₁; inj₂) public
import Axiom.Extensionality.Propositional as Axiom

open import Data.Bool using (true; false; Bool) public
open import Data.Nat using (zero; suc; ℕ) public

natElim : ∀ (P : ℕ → Set) → P zero → (∀ n → P n → P (suc n)) → ∀ n → P n
natElim P pz ps zero = pz
natElim P pz ps (suc n) = ps n (natElim P pz ps n)

coe : ∀ {i}{A B : Set i} → A ≡ B → A → B
coe refl x = x

J⁻¹ :
  ∀ {α β}{A : Set α} {x : A}(P : ∀ y → x ≡ y → Set β)
  → {y : A} → (w : x ≡ y) → P y w → P x refl
J⁻¹ P refl p = p

,≡ : ∀{i j}{A : Set i}{B : A → Set j}{a a' : A}{b : B a}{b' : B a'}
     (p : a ≡ a') → tr B p b ≡ b' → (Σ A B ∋ (a , b)) ≡ (a' , b')
,≡ refl refl = refl

tr-Σ : ∀ {I : Set}(A : I → Set)(B : ∃ A → Set)
         {i₀ i₁ : I}(i₀₁ : i₀ ≡ i₁)
         (ab : Σ (A i₀) (λ a → B (i₀ , a)))
       → tr (λ i → Σ (A i) λ a → B (i , a)) i₀₁ ab
         ≡ (tr A i₀₁ (₁ ab) , tr B (,≡ i₀₁ refl) (₂ ab))
tr-Σ A B refl ab = refl

tr-const : ∀ {A B}{a₀ a₁ : A}(a₀₁ : a₀ ≡ a₁)(b : B) → tr (λ _ → B) a₀₁ b ≡ b
tr-const refl b = refl

tr-swap :
  ∀ {A : Set}(B : A → Set)
    {a₀ a₁}(p : a₀ ≡ a₁) a b
  → a ≡ tr B (p ⁻¹) b → tr B p a ≡ b
tr-swap B refl a b q = q

tr-coe : ∀ {A : Set}(B : A → Set){a₀ a₁ : A}(p : a₀ ≡ a₁) b
         → tr B p b ≡ coe (ap B p) b
tr-coe B refl b = refl

coe-∘ : ∀ {A B C : Set}(p : A ≡ B)(q : B ≡ C) a → coe q (coe p a) ≡ coe (p ◾ q) a
coe-∘ refl refl a = refl

postulate
  ext  : ∀ {i j} → Axiom.Extensionality i j
  exti : ∀ {i j} → Axiom.ExtensionalityImplicit i j

UIP : ∀ {i}{A : Set i}{x y : A}(p q : x ≡ y) → p ≡ q
UIP refl refl = refl

UIP-refl : ∀ {i}{A : Set i}{x : A}(p : x ≡ x) → p ≡ refl
UIP-refl refl = refl

coe-UIP : ∀ {A : Set}(p : A ≡ A)(a : A) → coe p a ≡ a
coe-UIP refl a = refl

isLeft : ∀ {i j}{A : Set i}{B : Set j} → A ⊎ B → Set
isLeft (inj₁ _) = ⊤
isLeft (inj₂ _) = ⊥

isLeft-prop : ∀ {i j}{A : Set i}{B : Set j}{ab : A ⊎ B}{p q : isLeft ab} → p ≡ q
isLeft-prop {ab = inj₁ x} = refl

⊎-elim : ∀ {i j k}{A : Set i}{B : Set j}(P : A ⊎ B → Set k)
         → (∀ a → P (inj₁ a))
         → (∀ b → P (inj₂ b))
         → ∀ ab → P ab
⊎-elim P l r (inj₁ x) = l x
⊎-elim P l r (inj₂ y) = r y

lmap : ∀ {i j k}{A : Set i}{A' : Set j}{B : Set k}
        → (ab : A ⊎ B) → (isLeft ab → A → A')
        → A' ⊎ B
lmap (inj₁ a) f = inj₁ (f _ a)
lmap (inj₂ b) f = inj₂ b

case : {A B C : Set} → (A → C) → (B → C) → A ⊎ B → C
case f g (inj₁ a) = f a
case f g (inj₂ b) = g b

case-lmap : ∀ {A A' B}(f : A → A')(ab : A ⊎ B) →
  case (λ a → inj₁ (f a)) inj₂ ab ≡ lmap ab (λ _ → f)
case-lmap f (inj₁ _) = refl
case-lmap f (inj₂ _) = refl

lmap-isLeft→ :
  ∀ {A A' B}{ab : A ⊎ B}{f : isLeft ab → A → A'} → isLeft ab → isLeft (lmap ab f)
lmap-isLeft→ {ab = inj₁ x} p = p

lmap-isLeft← :
  ∀ {A A' B}{ab : A ⊎ B}{f : isLeft ab → A → A'} → isLeft (lmap ab f) → isLeft ab
lmap-isLeft← {ab = inj₁ x} p = p

lmap-lmap :
  ∀ {A A' A'' B : Set}(ab : A ⊎ B)
    (f  : isLeft ab → A → A')
    (f' : isLeft (lmap ab f) → A' → A'')
    → lmap {A' = A''}(lmap ab f) f'
    ≡ lmap ab (λ p a → f' (lmap-isLeft→ p) (f p a))
lmap-lmap (inj₁ x) f f' = refl
lmap-lmap (inj₂ y) f f' = refl

lmap-⊤ : ∀ {B}(ab : ⊤ ⊎ B) → lmap ab _ ≡ ab
lmap-⊤ (inj₁ x) = refl
lmap-⊤ (inj₂ y) = refl

getLeft : ∀ {A B} (ab : A ⊎ B) → isLeft ab → A
getLeft (inj₁ a) p = a

getLeft-lmap :
  ∀ {A A' B}(ab : A ⊎ B)(f : isLeft ab → A → A')(p : isLeft (lmap ab f))
  → getLeft (lmap ab f) p ≡ f (lmap-isLeft← p) (getLeft ab (lmap-isLeft← p))
getLeft-lmap (inj₁ x) f p = refl

⊎⊥ : ∀ {A : Set} → A ⊎ ⊥ → A
⊎⊥ (inj₁ a) = a
